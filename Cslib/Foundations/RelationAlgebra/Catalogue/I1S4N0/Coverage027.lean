/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1729–1792 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage027

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            333189689412179888922801949446053609472
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319849390849594084864035183725830471680
                            333193756669130721196836651618288009216)
                          256)
                        512)
                      1024))
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          3713820117856140824898699264
                          128)
                        (Code.joinWords 128
                          298577838553186727951017660915472400384
                          311922041479621234956341036481568047104))
                      512)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          4332827916430693919509970944
                          128)
                        (Code.joinWords 128
                          319845486485745381917478573879957913600
                          882690465950920696850184375967416320))
                      512)))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            16781756976904608541290863476680425472
                            128)
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128))
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            16781675847266193934609167687675281408
                            128)
                          (Code.joinWords 128
                            604462909807314587353088
                            606824093048749409959936))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            16781756976904608541290863476680425472
                            128)
                          4951760157141521099596496896)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          16823295985598187276433808195665788928
                          128)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            16823295985598187276433808195665788928
                            128)
                          4951760157141521099596496896)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          6189309760042031079839960135412744192
                          128)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            6189228630403616473158264346407731200
                            128)
                          2361183241434822606848)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            6189309760042031079839960135412875264
                            128)
                          4951760157141521099596496896)
                        512))))))
            32768)
          65536)
        131072)
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          59421121885698253195157962752
                          (Nat.shiftLeft
                            317238953462760898447956264722689425408
                            128))
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
                            317243101849350145328672662683929018368)
                          256)
                        512)
                      1024)
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            3503800510094245888
                            3506052309907931136)
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
                            3494793310839504896
                            1237940042782425385552314368)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            3503800510094245888
                            18892971983788488785920)
                          256)
                        512)
                      1024))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      39614081257132168796771975168
                      604462909807314587353088)
                    (Code.joinWords 512
                      39614081257132168796771975168
                      4951760157141521099596496896))
                  2048)
                4096)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          212679075474015807078423394893019742208
                          128)
                        (Code.joinWords 128
                          9223512774343131136
                          9799973526646554624))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212676479325586539664609129644855132160
                            128)
                          (Code.joinWords 128
                            140737488355328
                            149533581377536))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            606824093048749409959936
                            128)
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          212679075474015807078423394893019742208
                          128)
                        (Code.joinWords 128
                          140737488355328
                          149533581377536)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          170143779608898499145501568964048715776
                          212679075474015807078423394893019742208)
                        (Code.joinWords 128
                          9223372036854775808
                          9799832789158199296))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            212679075474015807078423394893019742208)
                          (Code.joinWords 128
                            9223512774343131136
                            9799973526646554624))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760157141521099596496896
                            18889465931478580854784)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            212676479325586539664609129644855132160)
                          (Nat.shiftLeft
                            12379400392853802748991242240
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13656026058366851157480964096
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 128
                          170143779608898499145501568964048715776
                          212679075474015807078423394893019742208)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 256
                        (Code.joinWords 128
                          170141183460469231731687303715884105728
                          212676479325586539664609129644855132160)
                        (Code.joinWords 128
                          140737488355328
                          149533581377536))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            212679075474015807078423394893019742208)
                          (Code.joinWords 128
                            140737488355328
                            149533581377536))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760157141521099596496896
                            18889465931478580854784)
                          256))))))))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          805306368
                          128)
                        (Nat.shiftLeft
                          311926108736572067230375738654607802368
                          128))
                      512)
                    1024)
                  2048)
                4096)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            39769428227294520451954376704
                            3497045110653190144)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            2361228277431096311808
                            1200209300694237184))
                        512)
                      1024))
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          32768
                          128)
                        256)
                      (Nat.shiftLeft
                        32768
                        256))
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      32768
                      32768)
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            12379400402653776275637796864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17340831956552240881985388544
                            128)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            3094850098213459483340832768
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            8056281661911888820241956864
                            128)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          212679075474015807078423394893019742208
                          (Nat.shiftLeft
                            9799832789158199296
                            128))
                        (Nat.shiftLeft
                          39768823762042841331134365696
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        212679075474015807078423394893019742208
                        (Nat.shiftLeft
                          9799973526646554624
                          128))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        212679075474015807078423394893019742208
                        (Nat.shiftLeft
                          39769428224952648645721718784
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          212676479325586539664609129644855164928
                          (Nat.shiftLeft
                            149533581377536
                            128))
                        (Nat.shiftLeft
                          606824093048749409959936
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          212679075474015807078423394893019774976
                          (Nat.shiftLeft
                            8796093022208
                            128))
                        (Nat.shiftLeft
                          2361183241434822606848
                          256))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          805306368
                          128)
                        (Code.joinWords 128
                          536870912
                          886838852540167577566582338045870080))
                      512)
                    1024)
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1197957500880551936
                            1200209300694237184)
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
                            3494793310839504896
                            18892962976589234044928)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            1197957500880551936
                            18890666140779275091968))
                        512)
                      1024))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          32768
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1024
                          128)
                        256))
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      32768
                      32768)
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9223512774343131136
                            9799973526646554624)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            140737488355328
                            149533581377536)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            604462909807314587353088
                            606824093048749409959936)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            8796093022208
                            128))
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        212679075474015807078423394893019742208
                        (Code.joinWords 128
                          9223372036854775808
                          9799832789158199296))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          212679075474015807078423394893019742208
                          (Code.joinWords 128
                            9223512774343131136
                            9799973526646554624))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760157141521099596496896
                            18889465931478580854784)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971026432
                          (Nat.shiftLeft
                            10522490333925732336642555904
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            11799115999438780745132277760
                            128)))
                      (Code.joinWords 512
                        42535295865117307932921825928971059200
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971059200
                          (Code.joinWords 128
                            140737488355328
                            149533581377536))
                        (Nat.shiftLeft
                          2361183241434822606848
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971059200
                          (Nat.shiftLeft
                            8796093022208
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760157141521099596496896
                            18889465931478580854784)
                          256)))))))))))
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          13835058055282163712
                          128)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            312254348478567463924566988246638133248
                            128)
                          256))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 128
                        9223372036854775808
                        140737488355328)
                      (Code.joinWords 128
                        9223372036854775808
                        1152921504606846976))
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17950130569638013986037301248
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17959801976194931019434950656
                            128)
                          256))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          39614685720041976111359328256
                          256)
                        (Code.joinWords 256
                          212679075474015807078423394893019742208
                          39769428224952648645721718784))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          604462909807314587353088
                          256)
                        (Code.joinWords 256
                          212676479325586539664609129644855132160
                          (Code.joinWords 128
                            606824093048749409959936
                            149533581377536)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          604462909807314587353088
                          256)
                        (Code.joinWords 256
                          212679075474015807078423394893019742208
                          606824093048749409959936))))
                  4096)))
            (Code.joinWords 16384
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
                          312258420806120697111519296405685403648
                          128)
                        256))
                    1024)
                  2048)
                4096)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17331160549995323848587739136
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17340831956570255280494870528
                            128)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17950130569638013986037301248
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17959801976194931294312857600
                            128)
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          170143779608898499145501568964048715776
                          39614081257132168796771975168)
                        (Code.joinWords 256
                          212679075474015807078423394893019742208
                          39768823762042841331134365696))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        170141183460469231731687303715884105728
                        (Code.joinWords 256
                          212676479325586539664609129644855132160
                          (Code.joinWords 128
                            2341871806232657920
                            2504001392817995776)))
                      (Code.joinWords 512
                        170143779608898499145501568964048715776
                        (Code.joinWords 256
                          212679075474015807078423394893019742208
                          (Nat.shiftLeft
                            18014398509481984
                            128)))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          170143779608898499145501568964048715776
                          (Code.joinWords 128
                            39614685720041976111359328256
                            1152921504606846976))
                        (Code.joinWords 256
                          212679075474015807078423394893019742208
                          (Code.joinWords 128
                            39769428224952648645721718784
                            274877906944)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          170141183460469231731687303715884105728
                          604462909807314587353088)
                        (Code.joinWords 256
                          212676479325586539664609129644855132160
                          606824093048749409959936))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          170143779608898499145501568964048715776
                          (Code.joinWords 128
                            604462909807314587353088
                            1152921504606846976))
                        (Code.joinWords 256
                          212679075474015807078423394893019742208
                          (Code.joinWords 128
                            606824093048749409959936
                            274877906944)))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            268435456
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          13835058055282163712
                          128)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            312254348478567463924566988246638133248
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1237940039285380274899124224
                          128)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        288371113640067072
                        128)
                      (Nat.shiftLeft
                        1441151880758558720
                        128)))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            604462909807314587353088
                            604462909807314587353088)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            604462909948052075708416
                            606824093198282991337472)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760157141521099596496896
                            4951760157141521099596496896)
                          256)
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          256)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            14236310451781873161339928576
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            14274996078009541294930526208
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237958928751311753479979008
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          604462909807314587353088
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            606824093189486898315264
                            149533581377536)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760157141521099596496896
                            18889465931478580854784)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760157141521099596496896
                            18889465931478580854784)
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
                          3723491524413057858296348672
                          128)
                        (Code.joinWords 128
                          298910145552132956919243612680542486528
                          45370289949877323818099476924725198848)))
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
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            2359886204742139904
                            2504001392817995776))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            18014398509481984
                            4951760157159535498105978880))))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            604462909807314587353088
                            604462909807314587353088)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            604462909807314587353088
                            606824093048749409959936)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760158294442604203343872
                            4951760158294442604203343872)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            4951760157141521374474403840
                            274877906944))))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          128))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          128)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2359886204742139904
                            2504001392817995776)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            4951760157141521099596496896
                            18889465931478580854784))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          (Code.joinWords 128
                            4951760157159535498105978880
                            18889483945877090336768)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            11760430373211112611541680128
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            11799115999438780745132277760
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            1152921504606846976
                            1237958929904233258086825984))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          (Code.joinWords 128
                            274877906944
                            18889465931753458761728))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          32768
                          5316911983139663491615228241121378304)
                        (Nat.shiftLeft
                          2361183241434822606848
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            4951760158294442604203343872
                            18890618852983187701760))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            81129638414606681695789005144064
                            128)
                          (Code.joinWords 128
                            4951760157141521374474403840
                            18889465931753458761728))))))))))
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
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            14289378425771877585832135436462456832
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
                            140737488355328
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            14289373355169476672914529449649635328
                            128)
                          (Nat.shiftLeft
                            149533581377536
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1152921504606846976
                            128)
                          256)
                        (Nat.shiftLeft
                          14289378425771877585832135436462456832
                          128))))
                  4096)
                8192)
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            333189689412179888922801949446053609472
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311039351013670314259490852105600630784
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            54043195541028864
                            128)
                          (Nat.shiftLeft
                            311922041479621234956341036481568047104
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332306998946228968225951765070086144000
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            63050944551583744
                            128)
                          (Nat.shiftLeft
                            13344202926434507005323375566095646720
                            128)))))
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332311055428149698560036554520343347200
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          333193756669130721196836651618288009216
                          128)
                        256))
                    1024))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          14330917434465456320975080155447820288
                          128)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          13666293295368196558687964651682004992
                          128)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1152921504606846976
                            128)
                          256)
                        (Nat.shiftLeft
                          14330917434465456320975080155447820288
                          128))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            8796093022208
                            128)
                          256)
                        (Nat.shiftLeft
                          13666288224765795645770358664869314560
                          128))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1152921504606846976
                            128)
                          256)
                        (Nat.shiftLeft
                          13666293295368196558687964651682136064
                          128)))))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          268435456
                          128)
                        256)
                      512)
                    1024)
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            140737488355328
                            604462909948052075708416)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            140737488355328
                            606824093198282991337472)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976)
                          256)
                        (Nat.shiftLeft
                          1152921504606846976
                          256)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13617340432139183023890366464
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          (Nat.shiftLeft
                            13656026058366851157480964096
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            1152921504606846976
                            1237940040438301779505971200))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            140737488355328
                            140737488355328)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          (Code.joinWords 128
                            140737488355328
                            149533581377536)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760158294442604203343872
                            18890618852983187701760)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            4951760158294442604203343872
                            18889465931478580854784)))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          59421121885698253195157962752
                          (Nat.shiftLeft
                            317238953462760898447956264722689425408
                            128))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18014398509481984
                          128)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        77975715365143581768548352
                        512)
                      (Nat.shiftLeft
                        5029131409596857366777692160
                        512))
                    2048))
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
                          316356262996809977751106080346722009088
                          128)
                        256)
                      (Code.joinWords 256
                        (Code.joinWords 128
                          36028797018963968
                          56294995354714112)
                        (Nat.shiftLeft
                          45370289949877323818099476924725198848
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
                            2368893403996880896
                            2513008592072736768)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014673387388928
                            274877906944)
                          256)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            140737488355328
                            604462909956848168730624)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            606824093048749409959936
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            274877906944
                            274877906944)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070602400912917605986812821504)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2332864606977916928
                            2476979795053772800)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760157141521099596496896
                            18889465931478580854784)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            5070602400912917605986812821504)
                          (Code.joinWords 128
                            4951760157159535772983885824
                            18889465931753458761728)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13617340432139183023890366464
                            128)
                          256)
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Nat.shiftLeft
                            13656026058366851157480964096
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            1237940040438301779505971200)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            5070602400912917605986812821504)
                          (Code.joinWords 128
                            274877906944
                            1237940039285380549777031168))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            8796093022208
                            128))
                        332306998946228968225951765070086144)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760158294442604203343872
                            18890618852983187701760)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            5070602400912917605986812821504)
                          (Code.joinWords 128
                            4951760157141521374474403840
                            18889465931753458761728))))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
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
                          805306368
                          128)
                        (Nat.shiftLeft
                          13348275253987740192275683725950320640
                          128)))
                    1024)
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            8046610255354971786844307456
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            8056281661911888820241956864
                            128)
                          256))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          39614685720041976111359328256
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            39769428224952648645721718784
                            1152921504606846976)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            604462909807314587353088
                            140737488355328)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            606824093048749409959936
                            149533581377536)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            1152921504606846976
                            128))
                        (Nat.shiftLeft
                          2361183241434822606848
                          256))))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          32768
                          64)
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      32768
                      32768)
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17331160549995323848587739136
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17340831956552241156863295488
                            128)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            8046610255354971786844307456
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            8056281661911889095119863808
                            128)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          212679075474015807078423394893019742208
                          39614081257132168796771975168)
                        (Nat.shiftLeft
                          39768823762042841331134365696
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        42535295865117307932921825928971026432
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            2314850208468434944
                            2476979795053772800)))
                      (Code.joinWords 512
                        42535295865117307932921825928971059200
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            274877906944
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          212679075474015807078423394893019742208
                          (Code.joinWords 128
                            39614685720041976111359328256
                            1152921504606846976))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            39769428224952648645721718784
                            274877906944)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971059200
                          (Code.joinWords 128
                            604462909807314587353088
                            8796093022208))
                        (Nat.shiftLeft
                          606824093048749409959936
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971059200
                          (Nat.shiftLeft
                            1152921504606846976
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2361183241434822606848
                            274877906944)
                          256))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
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
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        297747071055821155530452781502797185024
                        311039351013670314259490852105600630784)
                      256)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        298910145552132956919243612680542486528
                        312254348478567463924566988246638133248)
                      256))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            604462909948052075708416
                            604462909948052075708416))
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Code.joinWords 128
                            604462909948052075708416
                            606824093198282991337472)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            4951760158294442604203343872
                            4951760158294442604203343872))
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          4951760158294442604203343872)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            14236310451781873161339928576
                            128)
                          256)
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Nat.shiftLeft
                            14274996078009541294930526208
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            1237958928751311753479979008
                            128))
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            1152921504606846976
                            18890618852983187701760))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            604462909948052075708416
                            140737488355328))
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Code.joinWords 128
                            606824093189486898315264
                            149533581377536)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            4951760158294442604203343872
                            18890618852983187701760))
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            4951760158294442604203343872
                            18889465931478580854784)))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        297747071055821155530452781502797185024
                        316356262996809977751106080346722009088)
                      256)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        298577838553186727951017660915472400384
                        317238953462760898447956264722689425408)
                      256))
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1088
                          128)
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    32768
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          128)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2368893403996880896
                            2513008592072736768)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128))
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            18014673387388928
                            4951760157141521374474403840))))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            604462909948052075708416
                            604462909956848168730624))
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Code.joinWords 128
                            604462909807314587353088
                            606824093048749409959936)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            4951760158294442604203343872
                            4951760158294442604203343872))
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            4951760157141521374474403840
                            274877906944))))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        332312069548629881143557751882907648)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          128)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            2332864606977916928
                            2476979795053772800)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            4951760157141521099596496896
                            18889465931478580854784))
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            4951760157159535772983885824
                            18889465931753458761728)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            11760430373211112611541680128
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            131072)
                          (Nat.shiftLeft
                            11799115999438780745132277760
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            1152921504606846976
                            1237958929904233258086825984))
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            274877906944
                            18889465931753458761728))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            5316911983139663491615228241121378304)
                          (Nat.shiftLeft
                            8796093022208
                            128))
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          2361183241434822606848))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            4951760158294442604203343872
                            18890618852983187701760))
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            4951760157141521374474403840
                            18889465931753458761728)))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (1728 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage027
