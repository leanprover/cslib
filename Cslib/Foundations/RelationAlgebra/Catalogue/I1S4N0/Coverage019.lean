/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1217–1280 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage019

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3094887877145313644543737856
                            128)
                          (Code.joinWords 128
                            320177793484691610885704525645027999744
                            333521996411126117891027901211123646464))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            320181702919142714745178741477713379328
                            333526068798332586721044471366872465408)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          320181702919142714745178741477713379328
                          256)
                        512)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            329648542954659136480144150949525454848
                            128)
                          (Nat.shiftLeft
                            69556755972083082176650805248
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            329652599436579866814228940399782658048
                            128)
                          (Nat.shiftLeft
                            18014398509481984
                            128))
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            329652599436579866814228940399782658048
                            128)
                          (Nat.shiftLeft
                            29787932195322552031134089216
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            329652599436579866814228940399782658048
                            128)
                          (Nat.shiftLeft
                            18014398509481984
                            128))
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          116973523962564059735805545506762915840
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            116972063648879637444101105703056310272
                            128)
                          (Code.joinWords 128
                            19884411894892507517868310528
                            4951760171877299080352759808))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            116973523982371100364371629905148903424
                            128)
                          (Code.joinWords 128
                            77371252473350665690677248
                            18014398509481984))
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1170935903116328960
                            1170935903116328960)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            116973523962564059735805545506762915840
                            128)
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984))
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            116973523982371100364371629905148903424
                            128)
                          (Code.joinWords 128
                            19884411882192356569757253632
                            4952063570359056144208494592))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            116973523982371100364371629905148903424
                            128)
                          (Code.joinWords 128
                            77674664519875040395657216
                            18014398509481984))
                        512))))))
            32768)
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13871086852301127680
                            4951760171877299080352759808)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984)
                          256)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1171006271860506624
                            4951760158312531769503514624)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984)
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13871086852301127680
                            4951760171877299080352759808)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984)
                          256)
                        512))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1170935903116328960
                            1170935903116328960)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            303413217530646565486592
                            1181762631387318321152)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984)
                          256)
                        512)))))
              16384)
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
                            319679332986272267433365597997422870528
                            128)
                          (Nat.shiftLeft
                            62129115738640614739450789888
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319683237350120970379922207843295428608
                            128)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319683237350120970379922207843295428608
                            128)
                          (Nat.shiftLeft
                            1238243458537664054470639616
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319683237350120970379922207843295428608
                            128)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))
                        512)))
                  4096)
                8192)
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            337623910929368631717566993311207522304
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            45036546037907456
                            128)
                          (Nat.shiftLeft
                            338506601395319552414417177687174938624
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            337628048540927776658333478550469869568
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338510749781908799309833324832151830528
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          337628048540927776658333478550469869568
                          128)
                        256))
                    2048))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          107004161876105163301498812950275686400
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            107004161876105163301498812950275686400
                            128)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            61897001969168930139535310848
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            107002853660685727773368154370995126272
                            128)
                          (Nat.shiftLeft
                            62129115722787944051106643968
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039573610651050835968
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            107004161876105163306110498968703074304
                            128)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6189700201326817770148462592
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            107004161876105163306110498968703074304
                            128)
                          (Nat.shiftLeft
                            6190003609626422020598136832
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039573685417841524736
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            107004161876105163306110498968703074304
                            128)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))))))
                8192)))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          6917529027641081856
                          7205759403792793600)
                        256)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          (Code.joinWords 128
                            16140901064495857664
                            17005592192950992896))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            6917529027641081856
                            1187797380122277838848))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        512)))
                  4096))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        18014398509481984
                        128)
                      512)
                    1024)
                  2048)
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        18014398509481984
                        128)
                      512)
                    1024)
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          337623910929368631717566993311207522304
                          128)
                        256)
                      (Code.joinWords 256
                        (Code.joinWords 128
                          36028797018963968
                          38280596841037824)
                        (Nat.shiftLeft
                          338506601395319552414417177687174938624
                          128)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        18014398513676288
                        128)
                      512))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4647714815446351872
                            4935945191598063616)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984)
                          256)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4611686018427387904
                            4899916394579099648)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1171006271860506624
                            1171010669907017728)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          70368744177664
                          288305142942400512)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4647714815446351872
                            4951760162077466291194560512)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984))
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4611686018427387904
                            4899916394579099648)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          (Code.joinWords 128
                            1170935903116328960
                            1170935903116328960)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            288230376151711744
                            128)
                          256)
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4611686018427387904
                            4899916395652841472)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            1171006271860506624
                            1181762631387318321152)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            288305142942400512)
                          256)
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          298914054986584060778717828513227866112
                          317575413978552010852880482432513474560)
                        256)
                      512)
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5649305182326707979440481782009430016
                          128)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5649305182326707979440481782009430016
                          128)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106338239662793269832304564822427566080
                            332307018753269596792036163456073728)
                          (Code.joinWords 128
                            16140901064495857664
                            22360291976597773408316424192))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106339537737007903539211697446509871104
                            5649305182326707979440481782009430016)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106338239662793269832304564822427566080
                            5649305182327010210895385439303106560)
                          (Code.joinWords 128
                            19884411887938949693208264704
                            1238243458537664054470639616))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106339537737007903539211697446509871104
                            5649305182326707979440481782009430016)
                          77674664501860641886175232)
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          316360400608369122691872565585984356352
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          317575413918898775224515969619549224960
                          128)
                        256))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014718988379809496913694467282698240
                          337623910929368631717566993311207522304)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          128)
                        (Code.joinWords 128
                          319845486485745381917478573879957913600
                          338506601395319552414417177687174938624)))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014718988379809496913694467282698240
                          332306998946228968225951765070086144000)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          128)
                        (Code.joinWords 128
                          320177793484691610885704525645027999744
                          333521996411126117891027901211123646464)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5649305182326707979440481782009430016
                            128)
                          (Code.joinWords 128
                            1170935903116328960
                            6189700197597837277611950080)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5649305182326707979440481782009430016
                          128)
                        512)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            106338239662793269832304564822427566080
                            128)
                          (Nat.shiftLeft
                            69324642199981295394350956544
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663496226914259548766208
                            128)
                          (Nat.shiftLeft
                            69556755962283249387492605952
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          106339537737007903539211697446509871104
                          128)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5649305182326707979440481782009430016
                            128)
                          (Nat.shiftLeft
                            18014398509481984
                            128))))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            106338239662793269832304564822427566080
                            128)
                          (Nat.shiftLeft
                            29710560947749042992158081024
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5649305182326707979440552150753607680
                            128)
                          (Nat.shiftLeft
                            29787932195322552031134089216
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            106339537737007903539211697446509871104
                            128)
                          (Nat.shiftLeft
                            288305142942400512
                            128))
                        (Nat.shiftLeft
                          5649305182326707979440481782009430016
                          128)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          106339537737007903539211697446509871104
                          128)
                        (Code.joinWords 128
                          106339537737007903539211697446509871104
                          5649305182326707979440481782009430016))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            106338239682600310460870649220813553664
                            128)
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106338239662793269832304564822427566080
                            5316911983139663496226914259548766208)
                          (Code.joinWords 128
                            19884411885669135481013534720
                            6189700201362846566093684736)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          106339537756814944167777781844895858688
                          128)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106339537737007903539211697446509871104
                            5649305182326707979440481782009430016)
                          (Code.joinWords 128
                            77371252473350665690677248
                            18014398509481984)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            106338239662793269832304564822427566080
                            128)
                          (Nat.shiftLeft
                            22282920712036761342763335680
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106338239662793269836916250840854953984
                            332307018753269596792036163456073728)
                          (Code.joinWords 128
                            1170935903116328960
                            22360291960763117118481760256)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            106339537737007903539211697446509871104
                            128)
                          (Nat.shiftLeft
                            1237940039573610651050835968
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106339537737007903543823383464937259008
                            5649305182326707979440481782009430016)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            106338239682600310460870649220813553664
                            128)
                          (Nat.shiftLeft
                            6189700201326817770148462592
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106338239662793269836916250840854953984
                            5649305182327010210895455808047284224)
                          (Code.joinWords 128
                            19884411882192356569757253632
                            6190003609644436419107618816)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            106339537756814944167777781844895858688
                            128)
                          (Nat.shiftLeft
                            288305142942400512
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106339537737007903543823383464937259008
                            5649305182326707979440481782009430016)
                          77674664501860641886175232))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          536870912
                          128)
                        (Code.joinWords 128
                          536870912
                          317575413918898775209816220436382351360))
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          3909434451103859474215832685379584
                          4153457191647793634003948052414464)
                        256)
                      512)
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            6917529027641081856
                            7205759403792793600))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          (Code.joinWords 128
                            16140901064495857664
                            17005592192950992896))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            303418964053402346061824
                            1187797380122277838848))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        319014718988379809496913694467282698240
                        337623910929368631717566993311207522304)
                      256)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1170935903116328960
                            1170935903116328960)
                          256)
                        512)
                      16384)
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            4611686018427387904
                            128)
                          (Code.joinWords 128
                            4647714815446351872
                            4951760162077466291194560512)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984)
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            4611686018427387904
                            4951760162041437494175596544))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            70368744177664
                            128)
                          (Code.joinWords 128
                            1171006271860506624
                            4951760158312531769503514624)))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          16384
                          21267647932558653966460912964485513216)
                        (Code.joinWords 128
                          70368744177664
                          288305142942400512)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        106339537737007903539211697446509871104
                        21267647932558653966460912964485513216)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106338239662793269832304564822427566080
                            21267647932558653966460912964485513216)
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            4611686018427387904
                            128)
                          (Code.joinWords 128
                            4647714815446351872
                            4951760162077466291194560512)))
                      (Code.joinWords 512
                        (Code.joinWords 128
                          106339537737007903539211697446509871104
                          21267647932558653966460912964485513216)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106338239662793269832304564822427566080
                            21267647932558653966460912964485513216)
                          (Code.joinWords 128
                            4611686018427387904
                            4899916394579099648))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1170935903116328960
                            1170935903116328960)
                          256))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          106339537737007903539211697446509887488
                          21267647932558653966460912964485513216)
                        (Nat.shiftLeft
                          288230376151711744
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            106338239662793269832304564822427566080
                            21267647932558653966460912964485513216)
                          (Code.joinWords 128
                            4611686018427387904
                            4899916395652841472))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            70368744177664
                            128)
                          (Code.joinWords 128
                            303413217530646565486592
                            1181762631387318321152)))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          106339537737007903539211697446509887488
                          21267647932558653966460912964485513216)
                        (Code.joinWords 128
                          70368744177664
                          288305142942400512)))))))))))
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1237940039285380274899124224
                        128)
                      512)
                    1024)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          29710560942849126597578981376
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          29787932195304462864760176640
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
                            22282920707136844948184236032
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            22360291959592181215365431296
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            6190002427881805031789297664)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19884411881021420665567182848
                            6190003608473425749200601088)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          302231454903657293676544
                          256)
                        (Nat.shiftLeft
                          77674664501860641886175232
                          256))))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1237940039285380274899124224
                        128)
                      512)
                    1024)
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        2475880078570760549798248448
                        128)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          2485551485127677583330115584
                          128)
                        (Code.joinWords 128
                          320177793484691610885704525645027999744
                          333521996411126117891027901211123646464)))
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
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            69324642199981295394350956544
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Nat.shiftLeft
                            69556755957347304195894542336
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            29710560942849126597578981376
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            29787932195304467263880429568
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            6189700196426901374495621120)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            19884411881021420665567182848
                            6189700196426901374495621120)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          77371252455336267181195264)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            22282920707136844948184236032
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            22360291960745102719972278272)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            6190002427881805031789297664)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            19884411881021420666640924672
                            6190003608473430147247112192)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          302231454903657293676544
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          77674664501860641886175232))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        268435456
                        128)
                      256)
                    512)
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          128)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        302231454903657293676544
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          303412046524374704979968
                          1180591620717411303424)
                        256))
                    2048)
                  4096)))
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4951760157141525497643008000
                          128)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256)
                      512)
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        302231454903657293676544)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          303412046524374704979968
                          1180591625115457814528)
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
                            61897001964269013744956211200
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            62129115722787944051106643968
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6190002427881805031789297664
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6190003609626347253807448064
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256))))
                  4096)
                8192)
              16384)
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            61897001964269013744956211200
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            62129115722787944051106643968
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6190002427881879798579986432
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6190003608473430147247112192
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)))))
                8192)
              16384))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        268435456
                        128)
                      256)
                    512)
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1181744542222018150400)
                        256)
                      512))
                  4096)))
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          70368744177664
                          74766790688768)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4398046511104
                          128)
                        256))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256)
                      512)
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Code.joinWords 128
                          70368744177664
                          74766790688768))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1180591625115457814528
                          128)
                        256)))))
              16384)))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        536870912
                        128)
                      256)
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        536870912
                        128)
                      (Nat.shiftLeft
                        317575413918898775209816220436350894080
                        128)))
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            29710560942849126597578981376
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            29787932195304462864760176640
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            22282920707136844948184236032
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            19807040628566084398385987584)
                          (Code.joinWords 128
                            1152921504606846976
                            22360291960745102719972278272)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            6190002427881805031789297664)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            302231454903657293676544)
                          (Code.joinWords 128
                            19884411882174342170174029824
                            6190003609626347253807448064)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          302231454903657293676544)
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          77674664501860641886175232))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4137611559144940766485239262347264
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4153457191647793634003948052414464
                          128)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        319014718988379809496913694467282698240
                        256)
                      (Nat.shiftLeft
                        320177793484691610885704525645027999744
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128)
                          256))
                      16384))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            69324642199981295394350956544
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Nat.shiftLeft
                            69556755957347304195894542336
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            29710560942849201364369670144
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            29787932195304467263880429568
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        106339537737007903539211697446509871104
                        21267647932558653966460912964485513216)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          106338239662793269832304564822427566080
                          (Code.joinWords 128
                            19807040628566084398385987584
                            6189700196426901374495621120))
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Code.joinWords 128
                            19884411881021420665567182848
                            6189700196426901374495621120)))
                      (Code.joinWords 512
                        106339537737007903539211697446509887488
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          77371252455336267181195264))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          106338239662793269832304564822427566080
                          (Nat.shiftLeft
                            22282920707136844948184236032
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            19807040628566084398385987584)
                          (Code.joinWords 128
                            1152921504606846976
                            22360291960745102719972278272)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          106339537737007903539211697446509871104
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          106338239662793269832304564822427566080
                          (Code.joinWords 128
                            19807040628566084398385987584
                            6190002427881879798579986432))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            302231454903657293676544)
                          (Code.joinWords 128
                            19884411881021420666640924672
                            6190003608473430147247112192)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          106339537737007903539211697446509887488
                          302231454903657293676544)
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          77674664501860641886175232))))))))
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
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          4951760158294442604203343872)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        302231454903657293676544
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          303413199445879311826944
                          1181744542222018150400)
                        256)))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    16384
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          70368744177664
                          4951760157141595866387185664)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4951760157141525497643008000
                          128)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256)
                      512)
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Code.joinWords 128
                          302231454974026037854208
                          74766790688768))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          303412046524374704979968
                          1180591625115457814528)
                        256)))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (1216 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage019
