/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1345–1408 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage021

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338786985425680433106357824488952823808
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
                            338842980087993714470218907930754809856
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075523534013112748413203572064256
                            346845124364372782483665395619201024)
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            127609781817995824935627776723655852032
                            332312069548629881143557751882907648)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319679333035789869004780808993387839488
                            338838908463861222966218101781730164736)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            149539457790740072823129672444314386432
                            332312069626002314190514736475406336)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            128270501593244381749052439372335415296
                            21599954931504882934686864729555599360)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            149539457741222471250561539943742570496
                            332312069548629881143557751882907648)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            149539457790740677284886558256442376192
                            332393199264415740280589808069246976)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            149539457790740677286039479761049223168
                            332312069626002314190514736475406336)
                          256)
                        512)))))
              16384)
            32768)
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
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
                            332306998946228968225951765070086144
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          256)
                        512)
                      1024))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
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
                            332306998946228968225951765070086144
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          256)
                        512)
                      1024))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
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
                    2048)
                  4096)
                (Nat.shiftLeft
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
                            332306998946228968225951765070086144
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332312069626001133598894019064102912
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332312069626001133598894019064102912
                            128)
                          256)
                        512)))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338662370301075597243273092577051541504
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332312069626002314190514736475406336
                            128)
                          256)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332393199264415740280589808069246976
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332312069626002314190514736475406336
                            128)
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            5070602400912917605986812821504)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            180775007426748558714917760198126862336)
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            180775007426748558714917760198126862336))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            319014718988379809496913694467282698240
                            334965454997219921857457632385804795904)
                          (Code.joinWords 128
                            320177793554209681216824161707331944448
                            21278032595871165205292946286629093376)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            77372433046956984592498688)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21599954931504882934686864729555599360
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            5070679772165372942253994016768))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            77372433046956984592498688)
                          256)
                        512))))))))
        131072)
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338786985425680433106357824488952823808
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338843056209169157519278436516779524096
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212679075474015807089952750676576567296
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5331450096188115068910738716422569984
                            128)
                          256))))
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
                            127609781887320467119468171053510950912
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            138239711621052372667694187464313798656
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            26584559915698317458076141205606891520
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            159508819897006009868708666830084898816
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            329648542954659136491673365995593924608
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338838908394265781399792836833271873536
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            159508819901957770037379402975749865472
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098585158804324745216
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            159508819897006009880238022615789207552
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316998183380479011502760393091055616
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            159508819901957770037379543715385704448
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098585158804324745216
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
                            4056481920730334084789450257203200
                            128)
                          (Code.joinWords 128
                            336201221590130088947349637317001216
                            333767332437691888496475967162679296))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            5070602400912917605986812821504)
                          256)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338662370301075597243273092577051541504
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            332306999023600220681288032251281408)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            4137611559144940766485239262347264
                            128)
                          (Code.joinWords 128
                            333615214443035753423632629959229440
                            333858603358921815310390268723724288))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            77371252455336267181195264
                            5070679772165372942253994016768)
                          256)
                        512)))
                  4096))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
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
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            255211775190703847597530955573826158592
                            95704415758410944813343122085141020672)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            5070602400912917605986812821504)
                          256))
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            127605887595351923798765477786913079296
                            143556623606667916237880176255233425408)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          26584559915698317458076141205606891520
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            26584559915698317458076141205606891520
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          26584641050288492221899358094208532480)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584641045336732064757836994612035584)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            86200240815519599301775817965568)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993117729838255438445129723019264
                          128)
                        256))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5649218982085892459841180006191464448
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
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332306998946228968225951765070086144)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332306999023600220681288032251281408)
                          256)
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
                            3894222643901120721397872246915072
                            128)
                          (Nat.shiftLeft
                            5650689456782157205946916181909700608
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            86200240815519599301775817965568
                            128)
                          256)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            319845486485745381917478573879957913600)
                          (Code.joinWords 128
                            298743992052659842435130636798007443456
                            338838908394265781382643129452245024768))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21599954931504882934686864729555599360
                            332306999023600220681288032251281408)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            4056481921334796994596764844556288
                            128)
                          (Code.joinWords 128
                            21601263146924922930339016641850900480
                            333858603358921815310390268723724288))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629882296479256489754624
                            5070679772165372942253994016768)
                          256)
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
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
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584641045336732064757836994612035584)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21599960002107283847604470716368420864
                            86200240815519599301775817965568)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584641050288492221899358094208532480)
                          256)
                        (Nat.shiftLeft
                          21599960002107283848757392220975267840
                          256))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128)
                          (Nat.shiftLeft
                            313697807005240146005298466226161319936
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144000
                            128)
                          (Nat.shiftLeft
                            338838908394265781382643129452245024768
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            26584559915698317458076141205606891520
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            26586020249189780378346806145187840000
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3904363848702946556750583360913408
                            128)
                          (Nat.shiftLeft
                            5318387528438329150926942067048316928
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993117729838255438445129723019264
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606969926165156855808
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          256)
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            180775007466362639972049928994898837504)
                          (Code.joinWords 128
                            127605887595351923798765477786913079296
                            143556623606667916237880176255233425408))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            21599954931504882934686864729555599360
                            21267647932558653966460912964485513216)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584641045336732064757836994612035584)
                          256)
                        (Nat.shiftLeft
                          21599960002107283848757392220975267840
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          170141183460469231731687303715884105728
                          (Code.joinWords 128
                            127605887595351923798765477786913079296
                            26584559915698317458076141205606891520))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170805797458361689677362579282879053824
                            21267647932558653966460912964485513216)
                          (Code.joinWords 128
                            128602808592190610717314419934424465408
                            21267647932558653966460912964485513216)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584641050288492221899358094208532480)
                          256)
                        (Nat.shiftLeft
                          21599960002107283847604470716368420864
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584641045336732064757836994612035584)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21599960002107283847604470716368420864
                            86200240815519599301775817965568)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993117729838255438445129723019264
                            128)
                          256)
                        (Nat.shiftLeft
                          332312069548629882296479256489754624
                          256))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
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
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332306998946228968225951765070086144)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332306999023600220681288032251281408)
                          256)
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
                            4056481920730334084789450257203200
                            128)
                          (Code.joinWords 128
                            333615214365664500968296362778034176
                            333858603280908321013383729793466368))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            5070602400912917605986812821504)
                          256)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            298577838553186727951017660915472400384
                            319845486545166503803176827075115876352)
                          (Code.joinWords 128
                            320180389692774718405492860204481511424
                            345450063737093253422742677051408384))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            332306999023600220681288032251281408)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            4137611559749403676292553849700352
                            128)
                          (Code.joinWords 128
                            333615214443640216333439944546582528
                            333858603358921815310390268723724288))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070679772165372942253994016768
                            5070679772165372942253994016768)
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
                          5316993112778078098296924030126522368
                          128)
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            5070602400912917605986812821504)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        256)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584641046574672104043217269511159808)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            86200240815519599301775817965568)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          26584641051526432261184738369107656704)
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128)
                          (Code.joinWords 128
                            127605887595351923798765477786913079296
                            143556623607905856277165556530132549632))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          26584641046574672104043217269511159808)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584641046574672104043217269511159808)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            86200240815519599301775817965568)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          6646221115062179177448977533627269120
                          128)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            180775007466362639972049928994898837504)
                          (Code.joinWords 128
                            127605887595351923798765477786913079296
                            143556623607905856277165556530132549632))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647933796594005746293239384637440)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647933796594005746293239384637440)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          21267647932558653966460912964485513216))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          22596875934842755045612966467986259968)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647933796594005746293239384637440)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            5070602400912917605986812821504)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1329228002284101079152053503500746752
                          128)
                        256))))))))))
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5320806205783564612336626113368293376
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3904363848702946556609845872558080
                            128)
                          (Nat.shiftLeft
                            5318220198559099024357572838829326336
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
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
                            255211775190703847597530955573826158592
                            21267647932558653966460912964485513216)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85735205728127073816166642240383352832
                            21267647932558653966460912964485513216)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            81129638414606681695789005144064)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            81129638414606681695789005144064)
                          256))
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256)))
                  4096))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            5070602400912917605986812821504)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)))
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            336170067808978879981578454339025895424
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5318372316631126412173982819365683200
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3909434451103859474215832685379584
                            128)
                          (Nat.shiftLeft
                            5318387528438329150926942067048316928
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            288230376151711744
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606969926165156855808
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            21599954931504882934686864729555599360
                            21267647932558653966460912964485513216))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          21599960002107283848757392220975267840
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            127605887595351923798765477786913079296
                            21267647932558653966460912964485513216)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            128602808592190610717314419934424465408
                            21267647932558653966460912964485513216)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21599954931504882934686864729555599360
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            81129638414606681695789005144064)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5070602400912917605986812821504
                            128)
                          (Code.joinWords 128
                            21599960002107283847604470716368420864
                            86200240815519599301775817965568)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629882296479256489754624
                          256)
                        512)))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          128)
                        256)
                      512)
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
                        21267647932558653966460912964485513216
                        256))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        81129638414606681695789005144064
                        128)
                      256))
                  4096))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5070602400912917605986812821504)
                        256)
                      512)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256)
                      512))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5070602400912917605986812821504)
                        256)
                      512))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216))
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          128)
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          86200240815519599301775817965568)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216))
                      512))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256)
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256))
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          86517153465576656652149993766912
                          128)
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5387515050969974956360988622848))
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
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
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
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
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
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            336170067808978879981578454339025895424
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098585158804324745216
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316998183380479011502760393091055616
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098585158804324745216
                            128)
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
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
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
                            5316911983139663491615228241121378304
                            128)
                          256)
                        512)
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
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
                            5316911983139663491615228241121378304
                            128)
                          256)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098585154406278234112
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098585154406278234112
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
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
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
                            5316911983139663491615228241121378304
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
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          26584559915698317458076141205606891520
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            319014718988379809496913694467282698240)
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            337623910929368631734428470316082659328))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            320011639985218496415426607817775120384)
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            21278032526275723638867681338170802176)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            288234774198222848
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5070602400912917605986812821504
                            128)
                          (Nat.shiftLeft
                            81129638414606969926165156855808
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            288234774198222848
                            128)
                          256))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
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
                          5070602400912917605986812821504
                          128)
                        256)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          128)
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          86200240815519599301775817965568))))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256)
                      512))
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
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          128)
                        256))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256)
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        5070602400912917605986812821504
                        256)
                      512)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        21267647932558653966460912964485513216
                        21267647932558653966460912964485513216)
                      256))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          86517153465576656652149993766912
                          128)
                        (Nat.shiftLeft
                          81446551064663739046163180945408
                          128)))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
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
                          332312069548629881143557751882907648
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            81129638414606681695789005144064)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256)
                        512)))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5318372316631126411885752443213971456
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3904363848702946556609845872558080
                            128)
                          (Nat.shiftLeft
                            5318387528438329150638570403652435968
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
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
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            127605887595351923798765477786913079296
                            21267647932558653966460912964485513216))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            21267647932558653966460912964485513216)
                          (Code.joinWords 128
                            128602808592190610717332434332933947392
                            21267647932558653966460912964485513216)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          21599960002107283847622485114877902848
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            81129638414606681695789005144064)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21599960002107283847622485114877902848
                            86200240815519599301775817965568)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          415388819285187124375485195894128640
                          256)
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
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
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            81129638414606681695789005144064)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5070602400912917605986812821504
                            128)
                          (Code.joinWords 128
                            21599960002107283847622485114877902848
                            86200240815519599301775817965568)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          21599960002107283848775406619484749824
                          256))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            311039351013670314259490852105600630784
                            128)
                          (Nat.shiftLeft
                            337626507077797899146081148480597786624
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968239786823125368307712
                            128)
                          (Nat.shiftLeft
                            5329902866490802401275700122079985664
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5318372316631126412174123556854038528
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3909434451103859474356570173734912
                            128)
                          (Nat.shiftLeft
                            5318387528438329150926942067048316928
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606969926165156855808
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606969926165156855808
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          21267647932558653966478927362994995200))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          21350724682295211209692840408496734208
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            21267647932558653966460912964485513216)
                          (Code.joinWords 128
                            127605887595351923798765477786913079296
                            21267647932558653966460912964485513216))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170805797458361689677362579282879053824
                            21267647932558653966460912964485513216)
                          (Code.joinWords 128
                            128602808592190610717332434332933947392
                            21267647932558653966460912964485513216)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          21267647932558653966478927362994995200
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            81129638414606681695789005144064)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5070602400912917605986812821504
                            128)
                          (Code.joinWords 128
                            21267647932558653966478927362994995200
                            81129638414606681695789005144064)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          83076749736557243231927444011220992
                          256)
                        512)))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
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
                          86200240815519599301775817965568
                          128)
                        256)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        128)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        21267647932558653966460912964485513216))
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          128)
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5070602400912917605986812821504))
                      512))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5070602400912917605986812821504)
                        256)
                      512)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216))
                      512))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          86200240815519599301775817965568
                          128)
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          86200240815519599301775817965568))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256)
                      (Code.joinWords 128
                        21267647932558653966460912964485513216
                        21267647932558653966460912964485513216))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          128)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          128)))
                    2048))
                (Code.joinWords 4096
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
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256)
                      (Code.joinWords 128
                        21267647932558653966460912964485513216
                        21267647932558653966460912964485513216)))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        21267647932558653966460912964485513216)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        21267647932558653966460912964485513216))
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          86517153465576656652149993766912
                          128)
                        (Nat.shiftLeft
                          316912650057057350374175801344
                          128))
                      512))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (1344 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage021
