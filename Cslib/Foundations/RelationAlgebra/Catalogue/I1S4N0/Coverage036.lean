/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 2305–2368 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage036

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Nat.shiftLeft
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            311926801032256116886607430445258768384
                            311926801032256116886607430445258768384)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679724511123123941100333241915670528
                            128)
                          (Code.joinWords 128
                            311926801032256116881957463829998731264
                            3545906010155634368274225844958789632))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679724511123123941100333241915670528
                            128)
                          (Code.joinWords 128
                            51926296168173885187316681296314368
                            2693757525494787310969652510720))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679724511123123941100333241915670528
                            128)
                          (Code.joinWords 128
                            53221835081607125874094119646658560
                            38280596832649216))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212676479325586539673832501681709907968
                            128)
                          (Code.joinWords 128
                            2710378960155180022092919083852890112
                            39768823762042841333281849344))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679724511123123941100333241915670528
                            128)
                          (Code.joinWords 128
                            51923760866973418966961495564353536
                            38280596832649216))
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679724511123123941100333241915670528
                            128)
                          (Code.joinWords 128
                            51926296168173885187316681296314368
                            2693757525494787310969652510720))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679724511123123941100333241915670528
                            128)
                          (Code.joinWords 128
                            51926315975214513753401079682301952
                            2693757827726242214626946187264))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679724511123123941100333241915670528
                            128)
                          (Code.joinWords 128
                            10385385998694797938717524930592768
                            38280596832649216))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212676479325586539673832501681709907968
                            128)
                          (Code.joinWords 128
                            10384593717069655257060992658440192
                            9942205940510710332783591424))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679724511123123941100333241915670528
                            128)
                          (Code.joinWords 128
                            10384771980435312390101176038719488
                            302231493184254126325760))
                        512))))))
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
                            2485551485165958180028547072
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
                            39614081266355540833626750976
                            128)
                          (Nat.shiftLeft
                            43298345556560171000195289448448
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            9223372036854775808
                            128)
                          (Nat.shiftLeft
                            160941876523456185559441997824
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            39614081257132168796771975168
                            128)
                          (Nat.shiftLeft
                            198225148790609797115054915584
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2485551485165958180028547072
                            128)
                          256)
                        512)
                      1024)))
                8192))
            32768)
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            298582394489443948207486640066792521728
                            128)
                          (Code.joinWords 128
                            311926801032256116872157631040840531968
                            311926801032256116872157631040840531968))
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            830767497365572420564879412675215360
                            128)
                          (Nat.shiftLeft
                            9942205940510710332783591424
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            830780173871574702858894379707269120
                            128)
                          (Code.joinWords 128
                            38280596832649216
                            38280596832649216))
                        512))
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            830780173871574712082266416562044928
                            128)
                          (Code.joinWords 128
                            1300767972159201694443593734815744
                            2693757525494787310969652510720))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            830780173871574712082266416562044928
                            128)
                          (Code.joinWords 128
                            2693757525494787310969652510720
                            158456325038328507976246099968))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            830780173871574702858894379707269120
                            128)
                          (Code.joinWords 128
                            38280596832649216
                            38280596832649216))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            830767497365572420564879412675215360
                            128)
                          (Code.joinWords 128
                            10384593717069655257060992658440192
                            39768823762042841333281849344))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            830780173871574702858894379707269120
                            128)
                          (Code.joinWords 128
                            38280596832649216
                            38280596832649216))
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            830780173871574712082266416562044928
                            128)
                          (Code.joinWords 128
                            2693757525494787310969652510720
                            2693757525494787310969652510720))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            830780173871876943537170073855721472
                            128)
                          (Code.joinWords 128
                            178263365666894592374632087552
                            158456627269783411633539776512))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            830780173871574702858894379707269120
                            128)
                          (Code.joinWords 128
                            38280596832649216
                            38280596832649216))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            830767497365572420564879412675215360
                            128)
                          (Nat.shiftLeft
                            9942205940510710332783591424
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            830780173871876934313798037000945664
                            128)
                          (Code.joinWords 128
                            19807040628604364996292378624
                            302231493184254126325760))
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
                            311922041479621234956341036481568047104
                            311922041519390058718383877812702412800)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            311922041479621234966140869270726246400
                            45411828364514426210970395017799008256)
                          256))
                      (Nat.shiftLeft
                        85071889804449249572750784482024357888
                        256))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          85071889804449249572750784482024357888
                          1298074214633706907132624082305024)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889824256290201316868880410345472
                            1298074214935938362036281375981568)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        85071889804449249572750784482024357888
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85247129823424800005213688733135536128
                            176538103132390079880747207977074688)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9799832789158199296
                            9942205950310543124089274368)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889824256290201316868880410345472
                            302231454903657293676544)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544)
                          256))))))
              16384)
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
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
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        85071889804449249572750784482024357888
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            4611686018427387904)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633706907202992826482688
                            70368744177664)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            87739432315521517266908326971161182208
                            39768823762042841331134365696)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2668840585286901403514633310508679168
                            39768823764492799530571399168)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85071889804449249577362470500451745792
                            4611686018427387904)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            70368744177664)
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        85071889804449249572750784482024357888
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298094021674335473217022468292608
                            302231454903657293676544)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633711518818642509692928
                            4611686018427387904)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            70368744177664)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            9942205940510710332783591424
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2449958197289549824
                            9942205942960668530073141248)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298094021674340084903041969422336
                            302236066589676794806272)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566154768203907072
                            302231454974026037854208)
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
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311926801072024940634200472371974897664
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679724550737205189009130001832869888
                            128)
                          (Nat.shiftLeft
                            13515116018311327167295787339037540352
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            53221837567158610963491106009907200
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679724550737205189009130001832869888
                            128)
                          (Nat.shiftLeft
                            2485551485127677583195897856
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            51964365455004484312370124368642048
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679724550737205189009130001832869888
                            128)
                          (Nat.shiftLeft
                            40763044356093912364412724838400
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            218076468058462760398280845827244032
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212676479365200620921741298441627107328
                            128)
                          (Nat.shiftLeft
                            9799832791305682944
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            51923763352524904056358481927602176
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679724550737205189009130001832869888
                            128)
                          (Nat.shiftLeft
                            2485551485127677583195897856
                            128))))))
                8192)
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311926801094317532747894234353556783104
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311926801094317532747894234353556783104
                            128)
                          256))
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
                            51964365455004484312370124368642048
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679724550737205189009130001832869888
                            128)
                          (Nat.shiftLeft
                            40763044356093912364412724838400
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10385388484246283028114511293841408
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679724550737205189009130001832869888
                            128)
                          (Nat.shiftLeft
                            2485551485127677583195897856
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            51964365455004488924056142796029952
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679724550737205189009130001832869888
                            128)
                          (Nat.shiftLeft
                            40763044356093912434781469016064
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10384593717069655257060992658440192
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212676479365200620921741298441627107328
                            128)
                          (Nat.shiftLeft
                            2449958197289549824
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10384754658946173525099782443368448
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679724550737205189009130001832869888
                            128)
                          (Nat.shiftLeft
                            2485551485127747951940075520
                            128))))))
                8192)))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
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
                          2834994084760015885177650995754172416
                          176538132959007901412878206327848960)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2668840585286901410864507902377328640
                          39768823771842674122440048640)
                        256))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          1298074214633706907132624082305024)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298094021674335473217022468292608
                            1298074214935938362036281375981568)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544)
                          256))
                      1024))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            176538093190184139370036875193483264
                            176538103132390079880747207977074688)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9799832789158199296
                            9942205950310543124089274368)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544)
                          256)))
                    2048)))
              16384)
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        1298074214633706907132624082305024
                        256)
                      (Nat.shiftLeft
                        1298074214633706907132624082305024
                        256))
                    1024)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633711518818642509692928
                            4611686018427387904)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            70368744177664)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2668840585286901401064675113219129344
                            39768823762042841331134365696)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10384593717069657707019189947990016
                            39768823764492799530571399168)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4611686018427387904
                            4611686018427387904)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            70368744177664)
                          256)))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544)
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4611686018427387904
                            4611686018427387904)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            70368744177664)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            9942205940510710332783591424
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2449958197289549824
                            9942205942960668530073141248)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040633177770417887117312
                            302236066589676794806272)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566154768203907072
                            302231454974026037854208)
                          256))))))
              16384))))
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
                          2834994084760015885177650995754172416
                          176538132959007901412878206327848960)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2668840585286901410864507902377328640
                          39768823771842674122440048640)
                        256))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1298074214633706907132624082305024
                          1298074214633706907132624082305024)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298094021674335473217022468292608
                            302231454903657293676544)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544)
                          256))
                      1024))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            176538093190184139370036875193483264
                            10384603659275595767771325442031616)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9799832789158199296
                            9942205950310543124089274368)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544)
                          256)))
                    2048)))
              16384)
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        1298074214633706907132624082305024
                        256)
                      (Nat.shiftLeft
                        1298074214633706907132624082305024
                        256))
                    1024)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633711518818642509692928
                            4611686018427387904)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1298074214633706907202992826482688
                            70368744177664)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2668840585286901401064675113219129344
                            39768823762042841331134365696)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2668840585286901403514633310508679168
                            39768823764492799530571399168)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4611686018427387904
                            4611686018427387904)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            70368744177664)
                          256)))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544)
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4611686018427387904
                            4611686018427387904)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            70368744177664
                            70368744177664)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            9942205940510710332783591424
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2449958197289549824
                            9942205942960668530073141248)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040633177770417887117312
                            302236066589676794806272)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19807040628566154768203907072
                            302231454974026037854208)
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
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1338837258989800819497036807143424
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292482821559276502874478872088281088
                            128)
                          (Nat.shiftLeft
                            40763044356093912364412724838400
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2485551485127677583195897856
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292482781945195245742310075316305920
                            128)
                          (Nat.shiftLeft
                            2485551485127677583195897856
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40763044356093912364412724838400
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292482821559276502874478872088281088
                            128)
                          (Nat.shiftLeft
                            198225148790571516518222266368
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10384593717069655257060992658440192
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292279957849158729038070602803445760
                            128)
                          (Nat.shiftLeft
                            9799832791305682944
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2485551485127677583195897856
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292482781945195245742310075316305920
                            128)
                          (Nat.shiftLeft
                            2485551485127677583195897856
                            128))))))
                8192)
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311926801032256116872157631040840531968
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            311044097097517568750370055762401558528
                            128)
                          (Nat.shiftLeft
                            311926801032256116872157631040840531968
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292279957849158729038070602803445760
                            128)
                          (Nat.shiftLeft
                            2449958197289549824
                            128))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2485551485127677583195897856
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292482781945195245742310075316305920
                            128)
                          (Nat.shiftLeft
                            2485551485127677583195897856
                            128)))))
                  4096)
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40763044356093912364412724838400
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292482821559276502874478872088281088
                            128)
                          (Nat.shiftLeft
                            40763044356093912364412724838400
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2485551485127677583195897856
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292482781945195245742310075316305920
                            128)
                          (Nat.shiftLeft
                            2485551485127677583195897856
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            198225148795183202536649654272
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292482821559276502874549240832458752
                            128)
                          (Nat.shiftLeft
                            198225148790571586886966444032
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292279957849158729038070602803445760
                            128)
                          (Nat.shiftLeft
                            2449958197289549824
                            128))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2485551489739363602697027584
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292482781945195245742380444060483584
                            128)
                          (Nat.shiftLeft
                            2485551485127747951940075520
                            128))))))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          311922041479621234956341036481568047104
                          311922041549139305287460672543871991808)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          311922041479621234956341036481568047104
                          311922041549139305287460672543871991808)
                        256))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024))
                        (Code.joinWords 256
                          85071889804449249572750784482024357888
                          1298074214633706907132624082305024))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          1298074214633706907132624082305024)
                        85071889804449249572750784482024357888)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          1298074214633706907132624082305024)
                        85071889804449249572750784482024357888)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Code.joinWords 128
                            2834994084760015885177650995754172416
                            176538132959007901412878206327848960))
                        (Code.joinWords 256
                          85070591730234615865843651857942052864
                          (Code.joinWords 128
                            2668840585286901410864507902377328640
                            39768823771842674122440048640)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          128)
                        85071889804449249572750784482024357888))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          (Code.joinWords 128
                            1298074214633706907132624082305024
                            1298074214633706907132624082305024))
                        85071889804449249572750784482024357888)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889824256592432771772537704022016
                            128)
                          (Code.joinWords 128
                            1298094021674335473217022468292608
                            302231454903657293676544))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            302231454903657293676544)
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          128)
                        85071889804449249572750784482024357888)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          (Code.joinWords 128
                            10384593717069655257060992658440192
                            10384603659275595767771325442031616))
                        (Code.joinWords 256
                          85070591730234615865843651857942052864
                          (Code.joinWords 128
                            9799832789158199296
                            9942205950310543124089274368)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889824256592432771772537704022016
                            128)
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            302231454903657293676544)
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544))))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          311922041479621234956341036481568047104
                          311922041479621234956341036481568047104)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          311922041479621234973202513486443184128
                          311922041479621234973202513486443184128)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          9942205940510710332783591424
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2449958197289549824
                          9942205942960668530073141248)
                        256))
                    2048)
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          1298074214633706907132624082305024)
                        (Code.joinWords 256
                          85071889804449249572750784482024357888
                          1298074214633706907132624082305024))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          128)
                        85071889804449249572750784482024357888)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          (Code.joinWords 128
                            1298074214633711518818642509692928
                            4611686018427387904))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85071889804449249577362540869195923456
                            70368744177664)
                          (Code.joinWords 128
                            70368744177664
                            70368744177664)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Code.joinWords 128
                            10384593717069655257060992658440192
                            39768823762042841331134365696))
                        (Code.joinWords 256
                          85070591730234615870455337876369440768
                          (Code.joinWords 128
                            10384593717069657707019189947990016
                            39768823764492799530571399168)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          (Code.joinWords 128
                            4611686018427387904
                            4611686018427387904))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85071889804449249577362540869195923456
                            70368744177664)
                          (Code.joinWords 128
                            70368744177664
                            70368744177664))))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85071889804449249572750784482024357888
                          128)
                        85071889804449249572750784482024357888)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889824256592432771772537704022016
                            128)
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85071889804449249572750784482024357888
                            302231454903657293676544)
                          (Code.joinWords 128
                            19807040628566084398385987584
                            302231454903657293676544)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249572750784482024357888
                            128)
                          (Code.joinWords 128
                            4611686018427387904
                            4611686018427387904))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85071889804449249577362540869195923456
                            70368744177664)
                          (Code.joinWords 128
                            70368744177664
                            70368744177664)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          (Nat.shiftLeft
                            9942205940510710332783591424
                            128))
                        (Code.joinWords 256
                          85070591730234615870455337876369440768
                          (Code.joinWords 128
                            2449958197289549824
                            9942205942960668530073141248)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889824256592432771772537704022016
                            128)
                          (Code.joinWords 128
                            19807040633177770417887117312
                            302236066589676794806272))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            85071889804449249577362540869195923456
                            302231454974026037854208)
                          (Code.joinWords 128
                            19807040628566154768203907072
                            302231454974026037854208)))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (2304 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage036
