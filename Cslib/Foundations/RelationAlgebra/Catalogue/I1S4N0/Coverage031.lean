/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1985–2048 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage031

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            255211775190703847597530955573826158592
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            297749667273575065160389243209808609280
                            317241559821874352409694705053528489984)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319018613280349259528122210876489990144
                            909072745168073480208384)
                          256)
                        512)))
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249588891685546520215552
                            21267647932558653966460912964485513216)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            106339537766718464498201936214817243136
                            21267647932558653966460912964485513216)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615879678709913224216576
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85071889804449249588891896652752748544
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            95704415726224503808064136005480873984
                            10775030101939949912721977245696)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          116973361732998093712887296357574901760
                          256)
                        512)))))
              16384)
            32768)
          65536)
        131072)
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            4056481920730334084789450257203200
                            128)
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            5318210057354297198522360865203683328))
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            3894222643901120721397872246915072
                            4056481920730334084789450257203200)
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            5318291186993051815590823268664213504))
                        512)
                      1024)
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
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
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
                            42535295865117307932921825928971026432
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316922124344465317450440214747021312
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            42535295865117307932921825928971026432
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
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            26584559915698317458076141205606891520
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            42535295865117307932921825928971026432)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            42535295865117307932921825928971026432)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            5317085017446594645216762917260623872)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            42535295865117307932921825928971026432)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098585154406278234112
                            128)
                          256))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584559915698317458364371581758603264))
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            42535295865117307932921825928971026432)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            5316922124344465317738670590898733056)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            26584641045336732065046067370763747328
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            26584641045336732065046071768810258432))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            212676479325586539664609129644855132160)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            255876389188596305533982859103966330880
                            298411685053713613480739743088219521024)
                          (Code.joinWords 128
                            255876389188596305547853945956267458560
                            317238953462760898465153259899803664384)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            9903520314283042199192993792
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            5316993112778078098585158804324745216
                            128))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            42535295875020828247204868128164020224)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            173034306931153313304299987533824
                            128)
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            5316922758169765431853371339250335744)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316993112778078098585158804324745216
                            128)
                          256)
                        512)))))))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3894222643901120721397872246915072
                            128)
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128))
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            333183361359804671487327931098810286080
                            128)
                          (Code.joinWords 128
                            170808393606790957081953472494188888064
                            333193745956153308199362999104672104448))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            4056481921637028449500422138232832
                            128)
                          (Code.joinWords 128
                            830767497365572420564879412675215360
                            1947111322290570747465550578843648))
                        512)
                      1024))
                  4096))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10633823966279326983230456482242756608
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            664613997892457936451903530140172288
                            21267647932558653966460912964485513216)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10633986225556156196593848060253044736
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            43366073503687682179321917315271884800
                            21267647932558653966460912964485513216)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            55827738082243295875323288109784760320
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            664624139097259762287115503765815296
                            21267647932558653966460912964485513216)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            55827738094622696268177090858776002560)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            172400481631039198603551635931136
                            128)
                          (Code.joinWords 128
                            43366073503687682181663789121504542720
                            173034306931153313304299987533824)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            55827738094622696268177090858776002560)
                          256)
                        (Nat.shiftLeft
                          43366073503687682181663789121504542720
                          256)))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            180777603575177826128732025446291472384
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            333183209182311522227936556354549841920
                            128)
                          (Nat.shiftLeft
                            333193593776028591883806318552519016448
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13292279957849158729038070602803445760
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3904363848702946556820952105091072
                            128)
                          (Nat.shiftLeft
                            1947111321950560360769854623449088
                            128)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10633986225556156196593848060253044736
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            664624139097259762287115503765815296
                            21267647932558653966460912964485513216)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10633986228032036275164608610051293184
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            830777638570374248750970391788257280
                            21267647932558653966460912964485513216)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13292442230124358354897955067254538240
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            664624139097259762323144300784779264
                            21267647932558653966460912964485513216)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            55827738095241666287819780996225564672)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            173034306931153313304299987533824
                            128)
                          (Code.joinWords 128
                            43366073503687682181672796320759283712
                            173034306931153313304299987533824)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13293091257328154894068479180102696960
                            128)
                          256)
                        (Nat.shiftLeft
                          831426675677691099898693694615715840
                          256))))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            255211775190703847597530955573826158592
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            3894222643901120721397872246915072
                            4056481920730334084789450257203200)
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024))
                        512)
                      1024))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            298581732775830629071739058787719315456
                            333183361359804671487327931098810286080)
                          (Code.joinWords 128
                            3894282220672205695034573648297984
                            4137611560089414063059168305086464))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            3894222643901120721397872246915072
                            4056481921637028449500422138232832)
                          (Code.joinWords 128
                            1298074214935938362036281375981568
                            2028240960705177429161339583987712))
                        512)
                      1024))
                  4096))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10633986225556156196593848060253044736
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
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            55827575822966466661959896531774472192)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            5316922124344465317738670590898733056)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            55827738082243295875323288109784760320)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            288230376151711744
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10633823966279326983230456482242756608
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10633986225556156196593848060253044736
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            55827738082243295875323288109784760320)
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            55827738094622696268177090858776002560)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            172400481631039198603551635931136
                            128)
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            173034306931153313304299987533824)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          42535295865117307932921825928971026432
                          55827738094622696268177090858776002560)
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2475880078570760549798248448
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966749143340637224960)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            26584559915698317458076141205606891520
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            45193751869685510091225932935972519936)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            10141204801825835211973625643008
                            128)
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            5316922124344465317738670590898733056)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2658455994664681844021064807808499712
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            288230376151711744
                            128)
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
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
                      1024)
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
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            45193751856687139678729440049531715584
                            128)
                          256)
                        (Code.joinWords 256
                          85735205728127073816130613443364388864
                          95704415696513942862945195192485937152))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2658456002092322079733346457203245056
                            128)
                          256)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            53169119831396634916152282411213783040
                            45193751867209630012655172386174271488)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            10775030101939949912721977245696
                            128)
                          (Code.joinWords 128
                            172400481631039198603551635931136
                            10775030101939949912721977245696)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          10633823966279326983230456482242756608
                          2659105029296118618903870570051403776)
                        256))))))))))
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          255211775190703847597530955573826158592
                          128)
                        256)
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          255211775190703847597530955573826158592
                          128)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5649218982085892459841180006191464448
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5649218982085892459841180006191464448
                            128)
                          256)
                        512))))
                8192)
              16384)
            32768)
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
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
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            332469258223058181589343343080374272)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            332306998946228968225951765070086144)
                          256)
                        512)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3904363848702946556609845872558080
                            128)
                          (Nat.shiftLeft
                            333605073160862675133084389152391168
                            128)))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
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
                            21599954931582254187142200996736794624
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            162259276829213363391578010288128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            332469258300429434044679610261569536)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          42535295865117307932921825928971026432
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            21267647932558653966460912964485513216)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21599954931504882934686864729555599360
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            162259276829213363391578010288128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            332480033330531373994592332238815232)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          42535295865117307932921825928971026432
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            332312069626001133598894019064102912)
                          256)))))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3894222643901120721397872246915072
                            128)
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3904363848702946556609845872558080
                            128)
                          (Nat.shiftLeft
                            333610143763263588050761294465204224
                            128)))
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21599960002184655100059806983549616128
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            265845599156983174580761412056068915200
                            128)
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            265845599218880176545030425801025126400))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            308380895081521604399381491180197904384
                            128)
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            312254348551267427012912328296768733184)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            2305843009213693952
                            332312069626002314190514736475406336))
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
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
                            21599960002184656280651427700960919552
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            162259276829213363391578010288128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            173034306931153313304299987533824
                            128)
                          (Code.joinWords 128
                            42535295865117307935227668938184720384
                            332469892125729548159380358613172224)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332312069626002314190514736475406336
                            128)
                          256)
                        512)))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
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
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332469258223058181589343343080374272
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
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
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5649218982163263712584746649524371456
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220969518408402993152
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
                          85070591730234615865843651857942052864
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615879714738710243180544
                            332306998946228968225951765070086144)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128))
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306999023600220681288032251281408
                            128)
                          256)
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            332317140151030794061163738695729152)
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
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          256)
                        512)
                      1024))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            173034384302405768640567168729088)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            77371252455336267181195264
                            128)
                          256)
                        512))
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            288230376151711744
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          (Nat.shiftLeft
                            77372433335187360744210432
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            10141204801825835211973625643008
                            128)
                          (Nat.shiftLeft
                            5316911983217034744358794884454285312
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            288230376151711744
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            77372433335187360744210432
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932636025218916249231666708480
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            255211775190703847597530955573826158592
                            265845599156983174580761412056068915200)
                          (Code.joinWords 128
                            255211775250124969483229208768984121344
                            271162511202019840036645654042146504704))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            297747071055821155530452781502797185024
                            59421121885698253195157962752)
                          (Code.joinWords 128
                            69518070331119636062303944704
                            72699963088345340050130599936)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          (Nat.shiftLeft
                            77372433046956984592498688
                            128))
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85070591730234615879678709913224216576
                          256)
                        (Nat.shiftLeft
                          85070591730234615879714738710243180544
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            77372433046956984592498688
                            128))))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            10775030101939949912721977245696
                            128)
                          (Nat.shiftLeft
                            633902671366570037015532797952
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            77372433046956984592498688
                            128)
                          256)
                        512)))))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            255211775190703847597530955573826158592
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
                            297749667273575065160389243209808609280
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            312257106958973523656807346942964137984
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            319018613280349259528122210876489990144
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            72700910070399327909219139584
                            128)
                          256)))
                    2048))
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
                            85071889873773891772732079876375314432
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591789655737751541905053100015616
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85071889873774798467096790848256344064
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            106339537806333452440475232840382939136
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85735205797451716009194379813295489024
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            162893102129327478092326361890816
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          107004151804225910376927206742488514560
                          128)
                        256))))
                8192)
              16384))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
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
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5317074242416492704978619819131666432
                            128)
                          256))
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
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            5649218982163263712584746649524371456)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983217034744358794884454285312
                            128)
                          256)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            77371252455336267181195264
                            77371252743571041379418112)))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            332306999023600220969518408402993152))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            77371252455336267181195264
                            77371252743571041379418112)
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
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316922124344465317450440214747021312
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
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        256)
                      512)
                    1024)
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
                            21267647932558653966460912964485513216
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            173034306931153601534676139245568)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            288230376151711744
                            128)
                          256)
                        512)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85070591792131617830112665602898264064)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128))
                        512))
                    2048)
                  (Nat.shiftLeft
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
                          (Nat.shiftLeft
                            5316911983139663491903458617273090048
                            128)
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            21267647932558653966749143340637224960
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          85070591789655737751541905053100015616
                          85070591792131617830112665602898264064)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          (Nat.shiftLeft
                            288234774198222848
                            128))
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            255211775190703847597530955573826158592
                            297747071055821155530452781502797185024)
                          (Code.joinWords 128
                            255211775190703847611366013629108322304
                            16861477004875137024))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            255876389188596305533982859103966330880
                            13835058055282163712)
                          (Code.joinWords 128
                            256208696187542534516079897721337544704
                            17196995177114238976)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Nat.shiftLeft
                            288234774198222848
                            128))))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            162893102129327478092326361890816
                            128)
                          (Nat.shiftLeft
                            633825300114402931124503314432
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            288234774198222848
                            128)
                          256)
                        512))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            664624139097259762287115503765815296
                            332306998946228968225951765070086144)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            162259276829213363391578010288128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            43366063362482880353486705341646241792
                            332469258300429434044679610261569536)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          42535295865117307932921825928971026432
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            43366073503687682179321917315271884800
                            77371252455336267181195264)
                          256))))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            255211775190703847597530955573826158592
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3894222643901120721397872246915072
                            128)
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3904363848702946556609845872558080
                            128)
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21599954931504882934686864729555599360
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
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
                          (Code.joinWords 128
                            36028797018963968
                            21267647932636025218916249231666708480)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            162259276829213363391578010288128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          (Code.joinWords 128
                            42701449364590422419385680816993468416
                            332469258300429434044679610261569536)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166153499473114484158011878808748032
                            77371252455336267181195264)
                          256)
                        512))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            664613997892457936451903530140172288
                            21267647932558653966460912964485513216)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          42535295865117307932921825928971026432
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          43366073503687682179321917315271884800))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
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
                          (Code.joinWords 128
                            664624139097259762287115503765815296
                            21267647932558653966460912964485513216)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            162259276829213363391578010288128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            172400481631039198603551635931136
                            128)
                          (Code.joinWords 128
                            43366073503687682181663789121504542720
                            173034306931153313304299987533824)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          42535295865117307932921825928971026432
                          256)
                        (Nat.shiftLeft
                          43366073503687682181663789121504542720
                          256)))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            311043245236314215380212249977847545856
                            128)
                          (Nat.shiftLeft
                            3894222643901135133127786065035264
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            333183209182311522227936556354549841920
                            128)
                          (Nat.shiftLeft
                            3909434451103859474427488673726464
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3894222643901120721397872246915072
                            128)
                          (Nat.shiftLeft
                            1298074214633706907202992826482688
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3904363848702946556820952105091072
                            128)
                          (Nat.shiftLeft
                            1952181924351473278375841436270592
                            128)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
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
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            95704415755935064734772361535342772224
                            128)
                          (Nat.shiftLeft
                            85735205790024075766564569133038436352
                            128))
                        (Nat.shiftLeft
                          42701449364590422417034801811506069504
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          166153499473114486427826091003478016)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
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
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            43199909863009765869373729459111198720
                            172400481631039198603551635931136)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            162893102129327478092326361890816
                            128)
                          (Code.joinWords 128
                            42701449364590422419349652019974504448
                            162893102129327478092326361890816)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          664613997892457936451903530140172288
                          256)
                        (Nat.shiftLeft
                          166802536580431337575549393830936576
                          256))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5649218982085892459841180006191464448
                          128)
                        256)
                      512)
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
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332469258300429434044679610261569536)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            77371252455336267181195264
                            128)
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
                            5316911983139663491903458617273090048
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            5649218982163263712584746649524371456)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            288230376151711744
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            77371252455336267181195264
                            77371252743566643332907008)
                          256)))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21599954931504882934686864729555599360
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85070591730234615879678709913224216576
                          256)
                        (Code.joinWords 256
                          85735205728127073802295555388082225152
                          (Code.joinWords 128
                            85402898729180844847940690475313266688
                            332306998946228968225951765070086144)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21267647932558653966460912964485513216
                            128)
                          (Code.joinWords 128
                            77371252455336267181195264
                            77371252455336267181195264))))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306999023600220681288032251281408
                            332306999023600220681288032251281408)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            77371252455336267181195264
                            77371252455336267181195264)
                          256)
                        512))))))
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
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            5316922124344465317738670590898733056)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            288230376151711744
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
                            21267647932558653966460912964485513216
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        512)
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          162259276829213363391578010288128
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          172400481631039198603551635931136
                          128)
                        (Code.joinWords 128
                          10141204801825835211973625643008
                          173034306931153313304299987533824))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            95704415696513942849074108340184809472
                            128)
                          (Code.joinWords 128
                            85070591789655737751541905053100015616
                            90387503775271281321727893844019642368))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            288230376151711744
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            21267647932558653966460912964485513216
                            21267647932558653966460912964485513216)
                          (Nat.shiftLeft
                            288230376151711744
                            128))))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            26584559915698317458076141205606891520
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
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
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            288230376151711744
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            288230376151711744
                            128)
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
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
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 256
                        (Code.joinWords 128
                          85070591730234615865843651857942052864
                          95704415755935064734772361535342772224)
                        (Code.joinWords 128
                          85070591789655737751541905053100015616
                          91052117773163739258179797374159814656))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21267647932558653966460912964485513216
                          21267647932558653966460912964485513216)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          85070591730234615865843651857942052864
                          85070591730234615879678709913224216576)
                        (Code.joinWords 256
                          85735205728127073816130613443364388864
                          96036722695460171831171146957556023296))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)
                        (Nat.shiftLeft
                          21267647932558653966460912964485513216
                          128)))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10141204801825835211973625643008
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          633825300114114700748351602688
                          128)
                        (Code.joinWords 128
                          162259276829213363391578010288128
                          633825300114114700748351602688))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (1984 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage031
