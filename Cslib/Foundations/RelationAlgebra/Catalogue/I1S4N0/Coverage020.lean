/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1281–1344 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage020

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
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            333526068798332586721044471366872465408
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338838908394265781382643129452245024768
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853162258525401149369809647960064
                            56076500286422435283710161834737664)
                          256)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81803232538482839246701091356672
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            830777638725119112494005355485855744
                            4398046511104)
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075474015807078423394893019742208
                            128)
                          22430737640677658095157483607276126208)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212676479365200620921741298441627107328
                            128)
                          498460498612771583477268315558117376)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075513629888335555563689791717376
                            128)
                          498465589022213125005994697030631424)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21766108430977997421150719617578041344
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075474015807078423394893019742208
                            128)
                          498465569021744366454491135298502656)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075513629888335555563689791717376
                            128)
                          498465569215174857623151733467250688)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075513629888335555563689791717376
                            128)
                          498465589022215486189236132926980096)
                        512))))))
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
                            5070602400912917605986812821504
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
                          332306998946228968225951765070086144
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            5070602400912917605986812821504)
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
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            5070602400912917605986812821504)
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
                            332312069548629881143557751882907648
                            5070602400912917605986812821504)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            5070602400912917605986812821504)
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
                          332312069548629881143557751882907648
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21599954931504882934686864729555599360
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256)
                        512)))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223310303291865866647839586127097888768
                            128)
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            225968759283435698393647200247658577920))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            319014718988379809496913694467282698240
                            334965454937798799971759379190646833152)
                          (Code.joinWords 128
                            320177793554248366843051829840922542080
                            176538162746940096717341071088025600)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069626001133598894019064102912
                          256)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          332312069626001133598894019064102912)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069626002314190514736475406336
                          256)
                        512))
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
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            42535295865117307932921825928971026432)
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            45193751856687139678729440049531715584))
                        (Nat.shiftLeft
                          77371252455336267181195264
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5070679772165372942253994016768
                          256)
                        512)))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            77371252455336267181195264
                            4952062388596424756890173440)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          77372433046956984592498688
                          256)
                        512))
                    2048))))))
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
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338838908394265781382643129452245024768
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            225971517691141795032930532872205369344
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            56076487907059824784505537050968064
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5704427703545589333550969126912
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13292442217125987942977931729210179584
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1180591620717411303424
                            128)
                          256))))
                  4096)
                8192)
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338510749781908799309833324832151830528
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
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            39877083267414480164300820275022266368
                            128)
                          256)
                        (Nat.shiftLeft
                          212679075474015807078423394893019742208
                          128))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          29243015920266519616380248212608385024
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            7975449112394520099459509937531518976
                            128)
                          256)
                        (Nat.shiftLeft
                          212679075474015807078423394893019742208
                          128))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            7975367974709495238143418302061346816
                            128)
                          256)
                        (Nat.shiftLeft
                          212676479325586539673832501681709907968
                          128))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            7975449107442759947650250796741689344
                            128)
                          256)
                        (Nat.shiftLeft
                          212679075474015807087646766929874518016
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            7975449107442759943038573574407323648
                            128)
                          256)
                        (Nat.shiftLeft
                          212679075474015807087646766929874518016
                          128))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            7975449107442759947650259593908453376
                            128)
                          256)
                        (Nat.shiftLeft
                          212679075474015807087646766929874518016
                          128)))))
                8192)))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          (Code.joinWords 128
                            15211807202747976189997293240320
                            96975270917469349047286953410560))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5070602400912917605986812821504
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
                            319679332986272267433365597997422870528
                            319679332986272267433365597997422870528)
                          (Code.joinWords 128
                            320180399833978915768418264863519801344
                            179307339294083070442920951316217856))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            5070602402093509226704224124928)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            10775030101939949912721977245696
                            128)
                          (Code.joinWords 128
                            5070602400922140978023667597312
                            5704428005777044237208262803456))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            1180591620717411303424)
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
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          128)
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
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
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          26584559915698317458076141205606891520
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256)
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            63802943797675961899382738893456539648
                            71778311773623397176090961530037731328)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9223372036854775808
                            9799832789158199296)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          6646221109800934010486111365305991168)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993114016018137582304305025646592
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4611686018427387904
                            6646221109800934015097797383733379072)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          22596957062933744603187936913367498752)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            23926103935888916085479639696587882496)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9223372036854775808
                            9799832789158199296)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          1329309131922515685833749292505890816)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            1237940039285380274899124224)
                          256)
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4611686018427387904
                            1329227997332340926622218422331637760)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4952062388596424756890173440
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4611686018427387904
                            1329227997332340926622218423405379584)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984)
                          256)))))))))
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
                            86200240815519599301775817965568
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
                            5070602400912917605986812821504
                            5070602400912917605986812821504)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            5070602400912917605986812821504)
                          256)
                        512)
                      1024))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          173034306931153313304299987533824
                          128)
                        (Nat.shiftLeft
                          86834066115633714002524169568256
                          128))
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42701449364590422417034801811506069504
                            39614081257132168796771975168)
                          (Code.joinWords 128
                            21433801432031768450573888847020556288
                            39768823762042841331134365696))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400914070527491419668480
                            5070602402093509226704224124928)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            10775030101939949912721977245696
                            128)
                          (Code.joinWords 128
                            5070602403283324219458490204160
                            5704427703545589333550969126912))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            1237941219877000992310427648)
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
                            81129638414606681695789005144064
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256))
                      1024)
                    2048)
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
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
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
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014398509481984
                            1237940039303394673408606208)
                          256))
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            45193751856687139678729440049531715584
                            128)
                          (Nat.shiftLeft
                            23926103924128485712268527085046202368
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            9223372036854775808
                            128)
                          (Nat.shiftLeft
                            9799832789158199296
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81134590174763823216888601640960
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681700187051655168
                            128)
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81169252495863813873381870141440
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            162893102129327478092326361890816
                            128)
                          (Nat.shiftLeft
                            81803232538482839246701091356672
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4611686018427387904
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18018796555993088
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647937510414123602434064082010112)
                          256)
                        (Nat.shiftLeft
                          21267647932558653967613834469092360192
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            45193751856687139678729440049531715584)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            23926103934650976046194259421688758272))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            9223372036854775808
                            128)
                          (Code.joinWords 128
                            9223372036854775808
                            9799832789158199296)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            1237940039285380274899124224)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971026432
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            39614081257132168796771975168))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42701449364590422417034801811506069504
                            39614081257132168796771975168)
                          (Code.joinWords 128
                            21433801432031768452888739055488991232
                            39768823762042841331134365696)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4611686018427387904
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1170935903116328960
                            18014398509481984)
                          256)))
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940043897066294400253952
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628584098797969211392
                            1237940039303394673408606208)
                          256))
                      1024))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
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
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            5070602400912917605986812821504)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            298910145552132956919243612680542486528
                            317571260521360363059246478484461060096)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            5070602400912917605986812821504)
                          256)
                        512)))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          91904668516546631608510982389760
                          128)
                        (Code.joinWords 128
                          5070602400922140978023667597312
                          5704427701036832139524322623488))
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          21267647932558653966460912964485513216
                          (Code.joinWords 128
                            10141204804187018453408448249856
                            10775030104301133154156799852544))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602402093509226704224124928
                            5070602402093509226704224124928)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            10775030404171404816379270922240
                            128)
                          (Code.joinWords 128
                            5070602403283324219458490204160
                            5704428005777044237208262803456))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1180591620717411303424
                            1180591620717411303424)
                          256)
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
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
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319014718988379809496913694467282698240
                            128)
                          (Code.joinWords 128
                            319845486485745381917478573879957913600
                            338506601395319552414417177687174938624))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256)
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984))
                        512)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            130264343586921755544573091907473768448
                            128)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            23926103934650976046194259421688758272))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            9223372036854775808
                            128)
                          (Code.joinWords 128
                            9223372036854775808
                            9799832789158199296)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          (Nat.shiftLeft
                            1329228001046161039866673228601622528
                            128))
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        (Nat.shiftLeft
                          332393199187044487825253540888051712
                          128))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          (Code.joinWords 128
                            4611686018427387904
                            4611686018427387904))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984))))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            22596875933295329996506241124362354688))
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            130264343606728796173139176305859756032)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            23926103934650976046194259421688758272))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            9223372036854775808
                            128)
                          (Code.joinWords 128
                            9223372036854775808
                            9799832789158199296)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889824256290201316868880410345472
                            128)
                          (Nat.shiftLeft
                            1329228001046161039866673228601622528
                            128))
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          332306998946228968225951765070086144))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          (Code.joinWords 128
                            4611686018427387904
                            4611686018427387904))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548932112598461409176584192
                            128)
                          (Nat.shiftLeft
                            4952062388596424756890173440
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889824256290201316868880410345472
                            128)
                          (Code.joinWords 128
                            4611686018427387904
                            4611686019501129728))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984))))))))))))
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
                          332306998946228968225951765070086144
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            5070602400912917605986812821504)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
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
                            243428529325077177256163787407360
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5070602400912917605986812821504
                            128)
                          (Nat.shiftLeft
                            249133111768609120235433314222080
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          128)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            63802943797675961899382738893456539648
                            39614081257132168796771975168)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            64301404296095305351739680939571150848
                            39768823762042841331134365696)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          415388819285187123218060091659911168
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5070602400912917605986812821504
                            128)
                          (Code.joinWords 128
                            332312069548629881161572150392389632
                            5070602400912917605986812821504))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            1237940039285380274899124224)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            415388839092227751784144490045898752
                            1237940039285380274899124224)
                          256))))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        21267647932558653966460912964485513216
                        21267647932558653966460912964485513216)
                      256))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21599954931504882934686864729555599360
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256)
                        512))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            329648542954659136480144150949525454848
                            128)
                          (Nat.shiftLeft
                            337626669337074728359444399321119719424
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            329648542954659136480144150949525454848
                            128)
                          (Nat.shiftLeft
                            2671609768023099982946187123974209536
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681700187051655168
                            128)
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81169252495863813864585777119232
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            162893102129327478092326361890816
                            128)
                          (Nat.shiftLeft
                            81803232538482839317069835534336
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4398046511104
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          21350729752897612122587928397172703232
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216))
                        (Nat.shiftLeft
                          18014398509481984
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            1237940039285380274899124224)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076769543597870645090337790361600
                            1237940039285380274899124224)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            39614081257132168796771975168)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21433801432031768452906753453998473216
                            39768823762042841331134365696)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          83081820338958156149533430824042496
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1170935903116328960
                            1152991873351024640)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            1237940039285380274899124224)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076769543597870645090338864103424
                            1237940039285380274899124224)
                          256))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
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
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5070602400912917605986812821504)
                        256)
                      512)
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
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
                          5387515050969974956360988622848)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      21267647932558653966460912964485513216
                      256)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4952062388596424756890173440
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          128)
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5392467113358571381117878796288))))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256)
                      512)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        21267647932558653966460912964485513216
                        21267647932558653966460912964485513216)
                      256))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      21267647932558653966460912964485513216
                      256)
                    512))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        128)
                      (Code.joinWords 128
                        21267647932558653966460912964485513216
                        21267647932558653966460912964485513216))
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          81446551064663739046163180945408
                          128)
                        (Code.joinWords 128
                          1152991873351024640
                          316912650058210342247526825984))
                      512)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256)
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256))
                    (Code.joinWords 256
                      (Code.joinWords 128
                        21267647932558653966460912964485513216
                        21267647932558653966460912964485513216)
                      (Code.joinWords 128
                        21267647932558653966460912964485513216
                        21267647932558653966460912964485513216)))
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4952062388596424756890173440
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152991873351024640
                          4952062389749416630241198080)
                        256))
                    2048))))))
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
                            81129638414606681695789005144064
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
                          5316993112778078098296924030126522368
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        256))
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
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
                          256))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319014718988379809496913694467282698240
                            128)
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            337623910929368631734572585504158515200))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213341093323478997601061033174995304448
                            320011639985218496401591549762492956672)
                          (Code.joinWords 128
                            213507246822952112085174009057530347520
                            2668840585286901418070267306170122240)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          128)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098585154406278234112
                            128)
                          256)
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          128))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098585158804324745216
                          128)
                        256)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          128)
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
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
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          26584559915698317458076141205606891520
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        256))
                    2048)))
              (Code.joinWords 8192
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
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
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
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        81129638414606681695789005144064
                        128)
                      256)
                    1024)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971026432
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            288230376151711744))
                        (Code.joinWords 256
                          42535295865117307932921825928971026432
                          42701449364590422417034801811506069504))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606969926165156855808
                          128)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            288230376151711744
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1152991873351024640
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          288234774198222848
                          128)
                        256)))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
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
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
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
                          81446551064663739046163180945408)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256)
                      (Code.joinWords 256
                        21267647932558653966460912964485513216
                        21267647932558653966460912964485513216))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4952062388596424756890173440
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          5387515050969974956360988622848
                          128)
                        (Nat.shiftLeft
                          321864712445653775131065974784
                          128))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
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
                (Code.joinWords 4096
                  (Code.joinWords 2048
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
                      21267647932558653966460912964485513216
                      256)
                    (Nat.shiftLeft
                      21267647932558653966460912964485513216
                      256))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      21267647932558653966460912964485513216
                      256)
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
                          81129638414606681695789005144064
                          128)
                        (Code.joinWords 128
                          1152991873351024640
                          81446551064664892038036531970048)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        21267647932558653966460912964485513216
                        21267647932558653966460912964485513216)
                      256)
                    (Nat.shiftLeft
                      21267647932558653966460912964485513216
                      256))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        21267647932558653966460912964485513216
                        21267647932558653966460912964485513216)
                      (Code.joinWords 256
                        21267647932558653966460912964485513216
                        21267647932558653966460912964485513216))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4952062388596424756890173440
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152991873351024640
                          4952062389749416630241198080)
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
                            81129638414606681695789005144064
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
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
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81169252495863813864585777119232
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          167963704530240395698313174712320
                          128)
                        (Nat.shiftLeft
                          81803232538482839237868491112448
                          128)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            39614081257132168796771975168)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            127772041094825038282878453669448122368
                            39614081257132168796771975168)
                          (Code.joinWords 128
                            21433801432031768452888739055488991232
                            39768823762042841331134365696)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5316993112778078098296924030126522368)
                          83076749736557243213913045501739008)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          85070591730234615865843651857942052864
                          5316998183380479011214530016939343872)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            1237940039285380274899124224)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5316993112778078098296924030126522368)
                          (Code.joinWords 128
                            19807040628566084398385987584
                            1237940039285380274899124224)))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
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
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            316356262996809977751106080346722009088
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            317571260461707127430881965671496810496
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
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        21267647932558653966460912964485513216
                        21267647932558653966460912964485513216)
                      256))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144000
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319014718988379809496913694467282698240
                            128)
                          (Nat.shiftLeft
                            333521996411126117891027901211123646464
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976))
                        512)
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
                            128)))))))
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
                            162259276829213363400374103310336
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            162893102129327478101122454913024
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681700187051655168
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81129638414606681700187051655168
                            128)
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            81169252495863813873381870141440
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            162893102129327478162695106068480
                            128)
                          (Nat.shiftLeft
                            81803232538482839317069835534336
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4398046511104
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4398046511104
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5316993112778078098296924030126522368)
                          21350724682295211209670322410359881728))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Code.joinWords 128
                          85070591730234615865843651857942052864
                          5316911983139663491615228241121378304))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            1237940039285380274899124224)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            5316993112778078098296924030126522368)
                          (Code.joinWords 128
                            19807040628566084398385987584
                            1237940039285380274899124224)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971026432
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            39614081257132168796771975168))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            127772041094825038287490139687875510272
                            39614081257132168796771975168)
                          (Code.joinWords 128
                            21433801432031768452888739055488991232
                            39768823762042841331134365696)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            5316993112778078098296924030126522368)
                          83076749736557243213913045501739008)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85070591730234615870455337876369440768
                            5316993112778078098296994398870700032)
                          (Code.joinWords 128
                            1152921504606846976
                            1152991873351024640))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            1237940039285380274899124224)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            5316993112778078098296924030126522368)
                          (Code.joinWords 128
                            19807040628566084399459729408
                            1237940039285380274899124224)))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
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
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5070602400912917605986812821504)
                        256)
                      512)
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
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
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          316912650057057350374175801344)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256)
                      21267647932558653966460912964485513216)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4952062388596424756890173440
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          5387515353201429860018282299392
                          128)
                        (Nat.shiftLeft
                          321864712445653775131065974784
                          128))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
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
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256)
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256))
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        21267647932558653966460912964485513216
                        21267647932558653966460912964485513216)
                      256))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256)
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256))
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
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        128)
                      21267647932558653966460912964485513216)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          81446551064663739116531925123072
                          128)
                        (Code.joinWords 128
                          1152991873351024640
                          316912650058210342247526825984))
                      512)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        256)
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        256))
                    (Code.joinWords 128
                      21267647932558653966460912964485513216
                      21267647932558653966460912964485513216))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      21267647932558653966460912964485513216
                      21267647932558653966460912964485513216)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4952062388596424756890173440
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          302231454974026037854208
                          128)
                        (Code.joinWords 128
                          1152991873351024640
                          4952062389749416630241198080))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (1280 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage020
