/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 2497–2560 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage039

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Nat.shiftLeft
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311042799095723069597334397546949246976
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            308380895083997484492363770540802965504
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311044097169937703307123974673258250240
                            128)
                          256)
                        512)))
                  4096)
                8192)
              16384)
            32768)
          65536)
        (Code.joinWords 65536
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297747071115242277429986092756458536960
                            128)
                          (Nat.shiftLeft
                            309045509079568804855155586055507279872
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297751614374993495404161056940746604544
                            128)
                          (Nat.shiftLeft
                            309050224749705174185118038999837966336
                            128))
                        512))
                    2048)
                  4096)
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297747071115242277416151034697955147776
                            128)
                          (Nat.shiftLeft
                            308380895091425124713664533379390898176
                            128))
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297747071055821155544287839558079348736
                            128)
                          (Nat.shiftLeft
                            298411685053713613483045586097433214976
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297747071115242277429986092756458536960
                            128)
                          (Nat.shiftLeft
                            309045509079568804855155586055507279872
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297751614374994099867071004992822312960
                            128)
                          (Nat.shiftLeft
                            309050224749705781009211237282829303808
                            128))
                        512))))
                8192))
            32768)
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85736503802341707513814374030591918080
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
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            85735205728127073802295555388082225152))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            308380895081521604413216549238701293568
                            128)
                          (Code.joinWords 128
                            309045509019992940464546660322765701120
                            309045509082044684933726346605305528320))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889824256290205928554899911475200
                            128)
                          (Code.joinWords 128
                            85735205728127073806907241406509613056
                            85736513963508292473126342938039681024))
                        512)))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            255211775190703847597530955573826158592
                            128)
                          (Code.joinWords 128
                            225968759332953299965062411243623546880
                            311039351086089806557685598187199397888))
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615870455337876369440768
                            128)
                          (Code.joinWords 128
                            664624139097259762287115503765815296
                            85735215869331875632742453380135256064))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            265845599156983174594596470111351078912
                            128)
                          (Nat.shiftLeft
                            266510213154875632531624834393794674688
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889804449249577362470500451745792
                            128)
                          (Code.joinWords 128
                            664624139252004628381029472950812672
                            85736513963508294834309584372862287872))
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            308380895081521604399381491180197904384)
                          (Code.joinWords 128
                            311039351063187915830906063101565599744
                            311039351086089806557685598187199397888))
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128)
                          (Code.joinWords 128
                            85735215869486620498836367349320253440
                            85735215889293661127402451747706241024))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212676479325586539673832501681709907968
                            308380895081521604413216549238701293568)
                          (Code.joinWords 128
                            309045509059761764226589501656047550464
                            309045509082044684933726346605305528320))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889824256290205928554899911475200
                            128)
                          (Code.joinWords 128
                            85735215869486620498836367349320253440
                            85736513963508294834309584372862287872))
                        512))))))
            32768)))
      262144)
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
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
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096))
              16384)
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
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
                            42535295865117307932921825928971026432
                            127605887615158964431943248204800196608)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256)
                        512))
                    2048)
                  4096))
              16384))
          65536)
        (Code.joinWords 65536
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            298581096474650436402463838985881911296
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
                            298411685113289477871384697617980063744
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            298582394558923937391474493661328179200
                            128)
                          256)
                        512))
                    2048))
                8192)
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
                            1298074214633706907132624082305024
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
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
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
                            1298074214633706907132624082305024
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256)
                        512)
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            127605887615158964427331562185299066880)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
                          256)
                        512)))))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128)
                          (Nat.shiftLeft
                            181481159799509295272397907698900795392
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            266551751529743911138241559556842848256
                            128)
                          (Nat.shiftLeft
                            266551751529743911152076617612125011968
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
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
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
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
                            42535295865117307932921825928971026432))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            127605887615158964427331562185299066880)
                          (Code.joinWords 128
                            127605887595351923803377163805340467200
                            127605887615158964431943248204800196608)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            85070591730234615870455337876369440768
                            1298074214633706907132624082305024))
                        512)))))))))
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
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
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
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
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
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
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            266551751529743911138241559556842848256)
                          (Code.joinWords 128
                            181481159799509295272397907698900795392
                            266551751589165033023939812752000811008))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256)
                        512))
                    2048)
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            127605887595351923803377163805340467200
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            42535295865117307932921825928971026432)
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            127605887615158964427331562185299066880))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            127605887595351923803377163805340467200)
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            127605887615158964431943248204800196608)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)))))))))
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
                          (Nat.shiftLeft
                            95705713790535617184547325362653102080
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10633986225556156196593848060253044736
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          (Nat.shiftLeft
                            95704577975597812691003584316581085184
                            128)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            213507246822952112096703224103598817280
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            255211775190703847597530955573826158592
                            128)
                          (Nat.shiftLeft
                            298577838553186727967203597976241963008
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            255876389248017427419681112299124293632
                            128)
                          (Nat.shiftLeft
                            266510213214451496907822241315729440768
                            128))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10633986225556156197170317608649490432
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889824256290201316868880410345472
                            128)
                          (Nat.shiftLeft
                            95705876049812446403098872508560965632
                            128))))))
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          (Nat.shiftLeft
                            95704415696513942849074108340184809472
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309045509079568804840744067244700467200
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            298411685113134735366437996286598709248
                            128)
                          (Nat.shiftLeft
                            309045509079568804855191614852526243840
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            95704415716320983477640192738570797056
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889824256290205928554899911475200
                            128)
                          (Nat.shiftLeft
                            95705876049812446403098863712467943424
                            128))))
                    2048))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            95704577975597812691580053864977530880
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85070591750041656499021422274755428352
                            128)
                          (Nat.shiftLeft
                            95704577975597812696191739883404918784
                            128)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          (Nat.shiftLeft
                            298577838553186727962546875961540870144
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            298411685053713613480739743088219521024
                            128)
                          (Nat.shiftLeft
                            298577838553186727967203597976241963008
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212676479365200620921741298441627107328
                            128)
                          (Nat.shiftLeft
                            309045509079568804850543900036006150144
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            298411685113134735366437996286598709248
                            128)
                          (Nat.shiftLeft
                            309045509079568804855191614852526243840
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            95704577975597812691580053864977530880
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            85071889824256290205928554899911475200
                            128)
                          (Nat.shiftLeft
                            95705876049812446403098872508560965632
                            128))))))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
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
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85070591730234615865843651857942052864
                            1298074214633706907132624082305024)
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
                            1298074214633706907132624082305024
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            266551751589165033023939812752000811008)
                          (Code.joinWords 128
                            266551751569357992395373728353614823424
                            266551751591795655607421245836161449984))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            85070591730234615870455337876369440768
                            1298074214633706907132624082305024))
                        512))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
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
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            127605887615158964427331562185299066880
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            127605887615158964431943248204800196608
                            128)
                          (Code.joinWords 128
                            127605887595351923803377163805340467200
                            127605887615158964431943248204800196608)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            85070591730234615870455337876369440768
                            1298074214633706907132624082305024)))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128)
                          (Nat.shiftLeft
                            266551751529743911147464931593697624064
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            266551751529743911152076617612125011968
                            128)
                          (Nat.shiftLeft
                            266551751529743911152689107161447399424
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128))))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591730234615865843651857942052864
                            128)
                          256)
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        (Nat.shiftLeft
                          85070591730234615870455337876369440768
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        (Nat.shiftLeft
                          85070591730234615870455337876369440768
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            42535295865117307932921825928971026432)
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            127605887615158964427331562185299066880))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42535295865117307932921825928971026432
                            127605887615158964431943248204800196608)
                          (Code.joinWords 128
                            127605887595351923803377163805340467200
                            127605887615158964431943248204800196608)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85070591750041656494409736256328040448
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Code.joinWords 128
                            85070591730234615870455337876369440768
                            1298074214633706907132624082305024)))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (2496 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage039
