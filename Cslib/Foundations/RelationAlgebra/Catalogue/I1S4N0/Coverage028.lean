/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1793–1856 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage028

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144000
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            298580444842820797190667138137262653440
                            311924810721933297914077531759240544256)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319849390849594084864035183725830471680
                            333193756728706585587445577347808362496)
                          256)
                        512)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          14451850667901943703281972478476288
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319018613211023710617635092339529613312
                            128)
                          10384593717069655257060992658440192)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655259312792472125440
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297749667204250422944267046750961795072
                            128)
                          (Code.joinWords 128
                            10384593717069655259453529960480768
                            149533581377536))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319018613211023710617635092339529613312
                            128)
                          (Code.joinWords 128
                            10384593717069656412234297078972416
                            4951760158294442604203343872))
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          319018613211023710617635092339529613312
                          128)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319018613270444832503333345534687576064
                            128)
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            329652599436579866814228940399782658048
                            128)
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            308383653489227701026559148006372802560
                            128)
                          (Code.joinWords 128
                            604462909948052075708416
                            606824093198282991337472))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            329652599496000988699927193594940620800
                            128)
                          (Code.joinWords 128
                            1152921504606846976
                            4951760158294442604203343872))
                        512))))))
            32768)
          65536)
        131072)
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            4543259751217974174964184288067584
                            128)
                          (Code.joinWords 128
                            4555936257220256468979151320121344
                            158456325028528675187087900672))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13835058055282163712
                            14699749183737298944)
                          256)
                        512)
                      1024))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13835058055282163712
                            158456325043228424370825199616)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13835058055282163712
                            1237940053985129461857648640)
                          256)
                        512)
                      1024))
                  4096))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        2658455991569831745807614120560689152
                        256)
                      (Nat.shiftLeft
                        2658496556389039049148462015063261184
                        256))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            81129638414606681695789005144064)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2658496556389039049148462015063261184
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4398046511104
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2658455991569831755030986157415464960
                            9799832789158199296)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            633825300114114841485839958016
                            149533581377536)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2658496556389039058371834051918036992
                            9799832789158199296)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976)
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          40564819207303340847894502572032
                          40564819207303340847894502572032)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9223372036854775808
                            39614081266932001585930174464)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10384593717069655401176180734296064
                            59575864390608925729520353280)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9223372036854775808
                            9799832789158199296)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9223372036854775808
                            9799832791305682944)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            140737488355328
                            1238546863378578557890461696)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9223372036854775808
                            9799832791305682944)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            6189700197579822879102468096)
                          256))))))))
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
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            311926108796147931620984664383322849280)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                8192)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            2535301200456458802993406410752)
                          (Code.joinWords 128
                            9223372036854775808
                            158456325042940193994673487872))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          212679075474015807078423394893019742208
                          (Code.joinWords 128
                            39769428236481863691790188544
                            16717361820020506624))
                        512)
                      1024))
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            225971517691141795020824857073833476096
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311926108736572067244787257461388083200
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
                          40564819207303340847894502572032
                          128)
                        256)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2535301200456458802993406410752
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4951760158294442604203343872
                            128)
                          256)
                        512)
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075474015807078423394893019742208
                            128)
                          (Nat.shiftLeft
                            39614081257132168796771975168
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Nat.shiftLeft
                            218032189419137600916608253952
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075474015807078423394893019742208
                            128)
                          (Nat.shiftLeft
                            49517601581215184522611523584
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            69479384704891967931934572544
                            128)
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075474015807078423394893019742208
                            128)
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128))
                        (Code.joinWords 256
                          212679075474015807078423394893019742208
                          2535301200456458802993406410752))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          212679075513629888335555563689791717376
                          128)
                        (Code.joinWords 256
                          212679075474015807078423394893019742208
                          (Code.joinWords 128
                            39768823762042841331134365696
                            4951760157141521099596496896)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075474015807078423394893019742208
                            128)
                          (Nat.shiftLeft
                            9799832789158199296
                            128))
                        (Code.joinWords 256
                          212679075474015807087646766929874518016
                          (Nat.shiftLeft
                            1152921504606846976
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212676479365200620921741298441627107328
                            128)
                          (Nat.shiftLeft
                            9799832791305682944
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212676479325586539673832501681709907968
                            604462909948052075708416)
                          (Code.joinWords 128
                            39768823762042841333281849344
                            606824093198282991337472)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075513629888335555563689791717376
                            128)
                          (Nat.shiftLeft
                            9799973528794038272
                            128))
                        (Code.joinWords 256
                          212679075474015807087646766929874518016
                          (Code.joinWords 128
                            39769428224952648647869202432
                            4951760158294442604203343872)))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            316356262996809977751106080346722009088
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
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            298581742917035430897574270761344958464
                            317243101908926009719281588413449371648)
                          256)
                        512)
                      1024)
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Nat.shiftLeft
                            158456325028528675187087900672
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            16140901064495857664
                            17005592192950992896))
                        512)
                      1024))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316995648079278554755727023532933120
                            128)
                          (Code.joinWords 128
                            13835058055282163712
                            159694265082513804645724323840))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            16140901064495857664
                            1237940056290972471071342592))
                        512)
                      1024))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        633825300114114700748351602688
                        256)
                      512)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          40564819207303340847894502572032
                          40564819207303340847894502572032)
                        256)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          212676479325586539664609129644855132160
                          225968759283435698393647200247658577920)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          297747071055821155530452781502797185024
                          128)
                        (Code.joinWords 128
                          298577838553186727951017660915472400384
                          311922041479621234956341036481568047104)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            1152921504606846976
                            6189700197579822879102468096))
                        512)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          212679075474015807078423394893019742208
                          128)
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128))
                      1024))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212676479325586539664609129644855132160
                            128)
                          (Code.joinWords 128
                            9223372036854775808
                            9799832789158199296))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615368978609733632
                            128)
                          (Code.joinWords 128
                            140737488355328
                            149533581377536)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075474015807078423394893019742208
                            128)
                          (Code.joinWords 128
                            9223512774343131136
                            9799973526646554624))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            1152921504606846976
                            4951760158294442604203343872))))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075474015807078423394893019742208
                            128)
                          (Code.joinWords 128
                            40564819207303340847894502572032
                            40564819207303340847894502572032))
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          212679075513629888335555563689791717376
                          128)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            212676479325586539664609129644855132160)
                          (Code.joinWords 128
                            9223372036854775808
                            42089961345502762135728422912))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            59421121885698253195157962752
                            128)
                          (Nat.shiftLeft
                            62051744469179686279318601728
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            212679075474015807078423394893019742208)
                          (Code.joinWords 128
                            9223372036854775808
                            9799832789158199296))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            1152921504606846976
                            1237940040438301779505971200))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            212676479365200620921741298441627107328)
                          (Code.joinWords 128
                            9223372036854775808
                            9799832791305682944))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983140267954525176293197086720
                            128)
                          (Code.joinWords 128
                            604462909948052075708416
                            1238546863378578557890461696)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            212679075513629888335555563689791717376)
                          (Code.joinWords 128
                            9223512774343131136
                            9799973528794038272))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            1152921504606846976
                            6189700197579822879102468096))))))))))))
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          256)
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256)))))
                (Code.joinWords 4096
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
                            77371252455336267181195264
                            1180591620717411303424)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        311039351013670314259490852105600630784
                        256)
                      (Nat.shiftLeft
                        10384593717069669668579800244027392
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          77371252455336267181195264
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          77371252455336267181195264
                          256)
                        512)))))
              16384)
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
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
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        298577838553186727951017660915472400384
                        10384653292934045865986722178793472)
                      256))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            288230376151711744
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4398046511104
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          288230376151711744
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          288230376151711744
                          128)
                        256))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        10384593755755281484729126249037824
                        128)
                      256)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      10384593717069655401176180734296064
                      256)
                    512)))
              16384))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4746083847254490879203656800927744
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            4543259751217974174964184288067584
                            128)
                          (Nat.shiftLeft
                            158456325028528675187087900672
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            59421121885698253195157962752
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            59653235643064261996701548544
                            128)
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5070602400912917605986812821504
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1180591620717411303424
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        166156034774314940571778875941453824
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166153539087195741245144679307018240
                            633825904577024508062938955776)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            39768823762042841331134365696
                            606824093048749409959936)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166156074388396197703947672713428992
                            4951760157141521099596496896)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            39768823762042841331134365696
                            4951760157141521099596496896)
                          256))))))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        166153499473114484112975882535043072
                        256)
                      (Nat.shiftLeft
                        166156034774314940571778875941453824
                        256))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            59421121885698253195157962752
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            218109560671592937183789449216
                            128)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            59421121885698253195157962752
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            59653235643082276398432256000
                            128)
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2535301200456458802993406410752
                          256)
                        (Nat.shiftLeft
                          2535301200456458802993406410752
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            39614081257132168796771975168
                            10384593755755281484729126249037824)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            39768823771266213367989141504
                            14411518807585587200)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            39614081257132168796771975168
                            4951760157141521099596496896)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            39768823762042841331134365696
                            4951760157141521099596496896)
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1170935903116328960
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            39614081257132168796771975168
                            604462909807314587353088)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            39768823762042841333281849344
                            606824111212681500819456)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            39614081257132168796771975168
                            4951760157141521099596496896)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            39768823762042841333281849344
                            4951760158312457002712825856)
                          256))))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        21267647932558653966460912964485513216
                        21267647932558653966460912964485513216)
                      256)
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          633825300114114700748351602688
                          633825300114114700748351602688)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128)
                          256)
                        512))
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
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            5070602400912917605986812821504)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1180591620717411303424
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            59421121885698253195157962752
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            59653235643064261996701548544
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            633825300114114700748351602688
                            635063844616309888337838080000)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1238546863378429024309084160
                            128)
                          256))
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
                          256))))))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        266884058528690140106467511321912934400
                        128)
                      256)
                    512)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          13835058055282163712
                          14699749183737298944)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18155135997837312
                            18163932090859520)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1170935903116328960
                            4951760158312457002712825856)
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10384594993695320770109401148162048
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            13835058055282163712
                            1237940053985129458636423168)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            61897001964269013744956211200
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014398509481984
                            62129115721653036945009278976)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            1170935903116328960
                            1237940040456316178015453184))
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            604462909807314587353088
                            1238544502195187589486477312)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            604462927962450585190400
                            1238546863396592956399943680)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            1170935903116328960
                            6189700197597837277611950080)))))))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          14451910243766319900688894413242368
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593726741061813978026056089600
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10384593717069655257060992658440192
                            128)
                          256)
                        (Nat.shiftLeft
                          319018613211023710617635092339529613312
                          128))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10384593727345524723785340643442688
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297749667204250422944267046750961795072
                            128)
                          (Nat.shiftLeft
                            606824093048749409959936
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10384598678501218955499125652586496
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319018613211023710617635092339529613312
                            128)
                          (Nat.shiftLeft
                            4951760158294442604203343872
                            128))))))
                8192)
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            319845486485745381917478573879957913600
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311042109421376410886668508931775528960
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311924810662357433537880124837305778176
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332311055428149698560036554520343347200
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            333193756669130721211248170425873596416
                            128)
                          256)))
                    2048))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          319018613211023710617635092339529613312
                          128)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319683237350120970379922207843295428608
                            128)
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319018613211023710631470150394811777024
                            128)
                          (Nat.shiftLeft
                            1152921504606846976
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            604462909948052075708416
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            298414291343347682720389220310009774080
                            128)
                          (Nat.shiftLeft
                            606824093198282991337472
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319683237350120970393757265898577592320
                            128)
                          (Nat.shiftLeft
                            4951760158294442604203343872
                            128))))))
                8192)))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
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
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          633825300114114700748351602688
                          256)
                        (Nat.shiftLeft
                          633825300114114700748351602688
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1152921504606846976
                            128)
                          256)
                        512))
                    2048))
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          59421121885698253195157962752
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          10384593717069655257060992658440192
                          59653235643064261996701548544)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1238544502195187589486477312
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1238546863378429024309084160
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6189700197579822879102468096
                            128)
                          256))))
                  4096))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        271868663512883574629856787797964226560
                        128)
                      256)
                    512)
                  2048)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
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
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13835058055282163712
                            14699749183737298944)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18014398509481984
                            128)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4398046511104
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          633825300114114700748351602688
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            633825300114132855884349440000
                            18163932090859520)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1170935903116328960
                            1170935903116328960)
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13871086852301127680
                            1237940054021158255655387136)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          (Nat.shiftLeft
                            6189700196444915773005103104
                            128)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            59421121885698253195157962752
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          (Code.joinWords 128
                            10384593717069655419190579243778048
                            59653235643082276395211030528)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          (Code.joinWords 128
                            1170935903116328960
                            1170935903116328960))
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            140737488355328
                            1238544502195328326974832640)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          (Code.joinWords 128
                            18155135997837312
                            1238546863396592956399943680)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          (Code.joinWords 128
                            1170935903116328960
                            6189700197597837277611950080))))))))))
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
                            298910145552132956919243612680542486528
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
                        633825300114114700748351602688
                        128)
                      256)
                    2048)
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Nat.shiftLeft
                            158456325028528675187087900672
                            128))
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            69324642199981295394350956544
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Nat.shiftLeft
                            69556755957347304195894542336
                            128)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      21267647932558653966460912964485513216
                      128)
                    1024)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          212679075474015807078423394893019742208
                          332312069548629881143557751882907648)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            39614081257132168796771975168
                            604462909807314587353088)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            332306998946833431135759079657439232)
                          (Code.joinWords 128
                            39768823762042841331134365696
                            606824093048749409959936)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            39614685720041976111359328256
                            4951760157141521099596496896)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            332312069548629881143557751882907648)
                          (Code.joinWords 128
                            39769428224952648645721718784
                            4951760158294442604203343872))))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311043407495591044593575641555857833984
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            312258420806120697125930815213270990848
                            128)
                          256))
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          212676479325586539664609129644855132160
                          311039351013670314259490852105600630784)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          297747071055821155530452781502797185024
                          128)
                        (Code.joinWords 128
                          213507246822952112085174009057530347520
                          311922041479621234956341036481568047104)))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2535301200456458802993406410752
                          256)
                        (Nat.shiftLeft
                          2535301200456458802993406410752
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          (Nat.shiftLeft
                            18014398509481984
                            128))
                        512)
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
                            4951760158312457002712825856
                            128)))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            59421121885698253195157962752
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332352634367837184484405646385479680
                            128)
                          (Nat.shiftLeft
                            218109560671610951582298931200
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            69324642199981295394350956544
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Nat.shiftLeft
                            69556755957365318597625249792
                            128)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2535301200456458802993406410752
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            332312069548629881143557751882907648)
                          2535301200456458802993406410752))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          170141183460469231731687303715884105728
                          39614081257132168796771975168)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            13835058055282163712)
                          (Code.joinWords 128
                            39768823771302242165008105472
                            14447547604604551168)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          170143779608898499145501568964048715776
                          (Code.joinWords 128
                            39614081257132168796771975168
                            4951760157141521099596496896))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            332312069548629881143557751882907648)
                          (Code.joinWords 128
                            39768823762042841331134365696
                            4951760157159535498105978880)))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807087646766929874518016
                            332312069548629881143557751882907648)
                          (Nat.shiftLeft
                            1170935903116328960
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          170141183460469231731687303715884105728
                          (Code.joinWords 128
                            39614081257132168796771975168
                            604462909948052075708416))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212676479325586539673832501681709907968
                            332306998946833431135899817145794560)
                          (Code.joinWords 128
                            39768823762042841333281849344
                            606824111212681500819456)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          170143779608898499145501568964048715776
                          (Code.joinWords 128
                            39614685720041976111359328256
                            4951760157141521099596496896))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807087646766929874518016
                            332312069548629881143557751882907648)
                          (Code.joinWords 128
                            39769428224952648647869202432
                            4951760158312457002712825856)))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        633825300114114700748351602688
                        633825300114114700748351602688)
                      256)
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        128)
                      21267647932558653966460912964485513216)
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5649218982085892459841180006191464448
                          128)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5649305182326707979440481782009430016
                            128)
                          (Nat.shiftLeft
                            4951760158294442604203343872
                            128))
                        512))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      21267647932558653966460912964485513216
                      128)
                    1024)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            59421121885698253195157962752
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332307058367350853924204960228048896
                            128)
                          (Nat.shiftLeft
                            59653235643064261996701548544
                            128)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5649305182326707979440481782009430016
                            128)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1238544502195187589486477312
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5649218982086496922750987320778817536
                            128)
                          (Nat.shiftLeft
                            1238546863378429024309084160
                            128)))
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
                          (Nat.shiftLeft
                            6189700197579822879102468096
                            128))))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        633825300114114700748351602688
                        256)
                      (Nat.shiftLeft
                        633825300114114700748351602688
                        256))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          297747071055821155530452781502797185024
                          316356262996809977751106080346722009088)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          297747071055821155530452781502797185024
                          128)
                        (Code.joinWords 128
                          298577838553186727951017660915472400384
                          317238953462760898447956264722689425408)))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          297747071055821155530452781502797185024
                          311039351013670314259490852105600630784)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          297747071055821155530452781502797185024
                          128)
                        (Code.joinWords 128
                          298910145552132956919243612680542486528
                          312254348478567463924566988246638133248)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5649218982085892459841180006191464448
                            128)
                          (Code.joinWords 128
                            18014398509481984
                            1237940039303394673408606208)))
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
                            6189700197597837277611950080)))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        21267647932558653966460912964485513216
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663505450286296403542016
                            128)
                          (Code.joinWords 128
                            13835058055282163712
                            14699749183737298944))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5649305182326707979440481782009430016
                            128)
                          (Nat.shiftLeft
                            18014398509481984
                            128))
                        512)))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5649218982085892459841320743679819776
                            128)
                          (Code.joinWords 128
                            18155135997837312
                            18163932090859520))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5649305182326707979440481782009430016
                            128)
                          (Code.joinWords 128
                            1170935903116328960
                            4951760158312457002712825856))
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5649305182326707979440481782009430016
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663505450286296403542016
                            128)
                          (Code.joinWords 128
                            13871086852301127680
                            1237940054021158255655387136)))
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
                          (Nat.shiftLeft
                            6189700196444915773005103104
                            128)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            61897001964269013744956211200
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332307058367350853924204960228048896
                            128)
                          (Code.joinWords 128
                            18014398509481984
                            62129115721653036945009278976)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5649305182326707979440481782009430016
                            128)
                          (Code.joinWords 128
                            1170935903116328960
                            1237940040456316178015453184))
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            604462909948052075708416
                            1238544502195328326974832640)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5649218982086496922751128058267172864
                            128)
                          (Code.joinWords 128
                            604462927962450585190400
                            1238546863396592956399943680)))
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
                            6189700197597837277611950080)))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (1792 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage028
