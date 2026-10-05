/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1665–1728 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage026

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            298580444842820797190667138137262653440
                            311924810662357433523468606029720190976)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            298581742917035430897574270761344958464
                            311926108736572067230375738653802496000)
                          256)
                        512)))
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          4344936211666724279313632264
                          128)
                        (Code.joinWords 128
                          319845486485745381917478573879957962880
                          128))
                      512)
                    1024)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        631059277838836429196754944
                        128)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        12108295236030360004460544
                        128)
                      512))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            319018613211023710617635092339529613312
                            41539008693578735142944718985494528)
                          (Code.joinWords 128
                            4951760158294442604203343872
                            1152921504606846976))
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            297747071055821155530452781502797185024
                            41539008693578735142944718985494528)
                          (Code.joinWords 128
                            2361183241984578420736
                            584115552256))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319018613211023710617635092339529613312
                          41539008693578735142944718985494528)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          319018613211023710617635092339529613312
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            319018613211023710617635092339529613312
                            131072)
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        319018613211023710617635092339529613312
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          297747071055821155530452781502797185024
                          (Code.joinWords 128
                            549755813888
                            584115552256))
                        512)
                      (Nat.shiftLeft
                        329652437177303037600865548821772369920
                        512))))))
            32768)
          65536)
        131072)
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          155651560458624941873430528
                          2228224)
                        (Code.joinWords 128
                          807403520
                          4148386589246880716397962080681984))
                      512)
                    1024)
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            211106232532992
                            224300372066304))
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
                            5316993112778078098296924030126653440
                            128)
                          (Code.joinWords 128
                            9218305487273984
                            18889475162978207662080))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126653440
                            128)
                          (Code.joinWords 128
                            211106232532992
                            224300372066304))
                        512)
                      1024))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        49517601571415210995965001728
                        4951760157141521099596496896)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        9903520314283042199193026560
                        2361183241434822606848)
                      9903520314283042199193026560)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            34816
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1024
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      32768
                      1024))
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        212676479325586539664609129644855132160
                        225968759283435698393647200247658577920)
                      256)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        298577838553186727951017660915472400384
                        311922041479621234956341036481568047104)
                      256))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            8796093022208
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            1152921504606846976
                            1237940040438301779505971200)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            2305843009213693952
                            2449958197289549824))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            549755813888
                            1237940039285380859014676480)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            2305843009213693952
                            2449958197289549824))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        42535295865117307932921825928971059200
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            1152921504606846976
                            4951760158294442604203343872)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971059200
                          (Nat.shiftLeft
                            8796093022208
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976)))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971026432
                          (Code.joinWords 128
                            2305843009213693952
                            618970022092648334739111936))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            59575864390608925729520353280
                            618970019642690137449562112)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971059200
                          (Code.joinWords 128
                            2305843009213693952
                            2449958197289549824))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            4951779046607452578177351680
                            128))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971059200
                          (Code.joinWords 128
                            2305843009213693952
                            2449958197289549824))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            549755813888
                            37926505816130953674752)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971059200
                          (Code.joinWords 128
                            2305843009213693952
                            2449958197289549824))
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128))))))))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            35782656
                            128))
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          213509853112586181324823486279320600576
                          311926108736572067230375738653802496000)
                        256)
                      512)
                    1024)
                  4096))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            830777638570374246400091386300858368
                            131072)
                          (Code.joinWords 128
                            2361192248634077347840
                            9227101580296192))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          830777638570374246400091386300858368
                          (Nat.shiftLeft
                            219902325555200
                            128))
                        512)
                      1024))
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
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
                          311926108736572067230375738653802496000
                          128)
                        256))
                    1024)
                  2048)
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Code.joinWords 256
                      32768
                      (Nat.shiftLeft
                        2048
                        128))
                    (Nat.shiftLeft
                      128
                      256))
                  1024))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292442217125987942401462180813733888
                            128)
                          (Nat.shiftLeft
                            618970019642698933542584320
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            619879075190642544153198592
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          13292442217125987942401462180813733888
                          128)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            909055547952406703636480
                            128)
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 128
                          32768
                          13292442217125987942401462180813733888)
                        (Code.joinWords 256
                          830777638570374246400091386300858368
                          (Nat.shiftLeft
                            4951760158294442604203343872
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            13292442217125987942401462180813733888)
                          (Nat.shiftLeft
                            8796093022208
                            128))
                        (Code.joinWords 256
                          830777638570374246400091386300858368
                          (Code.joinWords 128
                            9942205940510710332783591424
                            1152921504606846976)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            13292442217125987942401462180813733888)
                          (Nat.shiftLeft
                            2449958197289549824
                            128))
                        (Code.joinWords 256
                          830777638570374246400091386300858368
                          (Code.joinWords 128
                            2361183241434822606848
                            4951760157141521099596496896)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292279957849158729038070602803445760
                            128)
                          (Nat.shiftLeft
                            2449958197289549824
                            128))
                        (Code.joinWords 256
                          830767497365572420564879412675215360
                          (Code.joinWords 128
                            9942205940510710332783591424
                            37926505816130953674752)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292442217125987942401462180813733888
                            128)
                          (Nat.shiftLeft
                            2449958197289549824
                            128))
                        (Code.joinWords 256
                          830777638570374246400091386300858368
                          9942205940510710332783591424))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
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
                            270532608
                            2228224))
                        512)
                      1024))
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          298581742917035430897574270761344958464
                          311926108736572067230375738653802496000)
                        256)
                      512)
                    1024)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            211106232532992
                            224300372066304)
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
                            131072
                            128)
                          (Code.joinWords 128
                            9218305487273984
                            9231499626807296))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            211106232532992
                            259484744155136)
                          256)
                        512)
                      1024))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 256
                    32768
                    (Nat.shiftLeft
                      2048
                      128))
                  1024)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            13292442217125987942401462180813733888)
                          (Nat.shiftLeft
                            8796093022208
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760158294442604203343872
                            1237940040438301779505971200)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            13292279957849158729038070602803445760)
                          (Code.joinWords 128
                            2305843009213693952
                            2449958197289549824))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2361183241984578420736
                            1237940039285380859014676480)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292442217125987942401462180813733888
                            128)
                          (Code.joinWords 128
                            2305843009213693952
                            2449958197289549824))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 128
                          32768
                          13292442217125987942401462180813733888)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            4951760158294442604203343872)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            13292442217125987942401462180813733888)
                          (Nat.shiftLeft
                            8796093022208
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2305843009213693952
                            2449958197289549824)
                          256)
                        (Nat.shiftLeft
                          59575864390608925729520353280
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292442217125987942401462180813733888
                            128)
                          (Code.joinWords 128
                            2305843009213693952
                            2449958197289549824))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            13292279957849158729038070602803445760
                            128)
                          (Code.joinWords 128
                            2305843009213693952
                            2449958197289549824))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            549755813888
                            37926505816130953674752)
                          256))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          10633823966279326983230456482242756608
                          13292442217125987942401462180813733888)
                        (Code.joinWords 128
                          2305843009213693952
                          2449993381661638656)))))))))))
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256)
                    512))
                8192)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5649218982085892459841180006191464448
                          128)
                        512)
                      1024)
                    2048)
                  4096)
                8192))
            32768)
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            576680655467839488
                            128)
                          (Nat.shiftLeft
                            838860800
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            33685504
                            128)
                          (Nat.shiftLeft
                            4072327553233186952308159888359424
                            128)))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        11529215046068502528
                        1152921504606846976)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 128
                        2305843009213726720
                        8796093022208)
                      2305843009213726720))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            906694364710971881029632
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Nat.shiftLeft
                            910236139573124114939904
                            128)))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            2361183241434822606848
                            4951760157159535498105978880)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            9903520314283042199192993792
                            37778931862957161709568))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          (Code.joinWords 128
                            9942205940510710332783591424
                            37926523829945347604480)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          9903520314283042199192993792)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            9942205940510710332783591424
                            18014398509481984)))))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        32768
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            32896
                            64)
                          256))
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          212676479325586539664609129644855132160
                          311039351013670314259490852105600630784)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          213507246822952112085174009057530347520
                          311922041479621234956341036481568047104)
                        256)))
                  (Nat.shiftLeft
                    32768
                    1024))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            619876714007401109330591744
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751883038720
                            128)
                          (Nat.shiftLeft
                            619880255782263536442408960
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            906694364710971881029632
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751883038720
                            128)
                          (Nat.shiftLeft
                            910236139573124114939904
                            128)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971059200
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Nat.shiftLeft
                            4951760158294442604203343872
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971026432
                          (Code.joinWords 128
                            9903520314283042199192993792
                            14411518807585587200))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            9942205940519717532038332416
                            9007199254740992)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971059200
                          9903520314283042199192993792)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            9942205940510710332783591424
                            1152921779484753920)))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971059200
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            2361183241434822606848
                            4951760157141521099596496896)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971059200
                          (Code.joinWords 128
                            9903520314283042199192993792
                            37778931862957161709568))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          (Code.joinWords 128
                            9942205940510710332783591424
                            37926505816130953674752)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          42535295865117307932921825928971059200
                          9903520314283042199192993792)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          9942205940510710332783591424))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 128
                        32768
                        288379909733089280)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            268435456
                            288234774466658304)
                          (Code.joinWords 128
                            268435456
                            268435456))
                        (Nat.shiftLeft
                          268435456
                          256)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 128
                          16140901064495857664
                          4332790139804673971595509760)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            4344879395694977253927682048
                            128)
                          298910145552132956919243612680542486528))
                      (Code.joinWords 512
                        (Code.joinWords 128
                          1152921504606846976
                          1237958929904233258153935872)
                        (Nat.shiftLeft
                          18889465931478580854784
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 128
                        32768
                        8796093022208)
                      (Code.joinWords 128
                        1152921504606846976
                        4398046511104)))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          (Code.joinWords 128
                            2361201255833332088832
                            1237940039303394673408606208)))
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
                            18014398509481984
                            1237940039303394673408606208))))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          59421121885698253195157962752
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            59653235643082276395211030528
                            18014398509481984)
                          256))
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
                          (Code.joinWords 128
                            18014398509481984
                            4951760157159535498105978880))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            37778931862957161709568
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          (Code.joinWords 128
                            18014398509481984
                            37926523829945347604480)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984))
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1237958928751311753479980032
                          128)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            18889465931478580855808
                            128)
                          (Code.joinWords 128
                            64
                            64)))
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          297747071055821155530452781502797185024
                          311039351013670314259490852105600630784)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          298577838553186727951017660915472400384
                          311922041479621234956341036481568047104)
                        256)))
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        1856910058928070412348686336
                        128)
                      (Nat.shiftLeft
                        621387871281919395799105536
                        128))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        1237958928751311753479980032
                        128)
                      (Nat.shiftLeft
                        18889465931478580854784
                        128))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            13835058055282163712
                            1237940053985129458636423168))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            9007199254740992
                            1237940039294387474153865216)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            4951760157141521099596496896
                            1237940039285380274899124224))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            4951760158294442879081250816
                            1237940040438302054383878144))))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            5316911983139663491615228241121378304)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          (Code.joinWords 128
                            2361183241984578420736
                            1237940039285380859014676480)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
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
                          (Code.joinWords 128
                            1152921504606846976
                            4951760158294442604203343872)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13835058055282163712
                            14699749183737298944)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            9007199254740992
                            9007199254740992)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            1152921779484753920
                            1152921779484753920))
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          59421121885698253195157962752
                          256)
                        (Nat.shiftLeft
                          59653235643064261996701548544
                          256))
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
                            128))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            37778931862957161709568
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          (Code.joinWords 128
                            549755813888
                            37926505816130953674752)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        512)))))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
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
                            311924810662357433523468606029720190976
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311043407495591044593575641555857833984
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311926108736572067230375738653802496000
                            128)
                          256)))
                    2048))
                8192)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319018613211023710617635092339529613312
                            128)
                          (Nat.shiftLeft
                            4951760158294442604203343872
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735142944718985494528
                            128)
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297747071055821155530452781502797185024
                            128)
                          (Nat.shiftLeft
                            37778931871753254731776
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            41539008693578735142944718985494528
                            128)
                          (Nat.shiftLeft
                            37926505815546838122496
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          319018613211023710617635092339529613312
                          128)
                        (Nat.shiftLeft
                          41539008693578735142944718985494528
                          128))))
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306998946228968225951765070086195200
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          65866003544408264
                          128)
                        (Nat.shiftLeft
                          2048
                          128)))
                    1024)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        11821949021978624
                        128)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2815059004882944
                        128)
                      512)))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319018613211023710617635092339529613312
                            128)
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        319018613211023710617635092339529613312
                        128)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319018613211023710617635092339529613312
                            128)
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            297747071055821155530452781502797185024
                            128)
                          (Nat.shiftLeft
                            37778931862957161709568
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            37926505815546838122496
                            128)
                          256))
                      (Nat.shiftLeft
                        319683227208916168554086995869669785600
                        128))))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      32768
                      77978076548385016591155200)
                    (Code.joinWords 512
                      (Code.joinWords 256
                        268435456
                        (Code.joinWords 128
                          268435456
                          268435456))
                      (Code.joinWords 256
                        77372433046956984860934144
                        268435456)))
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            1237940039285389070992146432
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            18014398509481984
                            1237940039303394673408606208)))
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
                          (Code.joinWords 128
                            18014398509481984
                            1237940039303394673408606208))))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            59421121885698253195157962752
                            618970019642690137449562112)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            131072)
                          (Code.joinWords 128
                            59653235643082276395211030528
                            618970019660704535959044096)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            4951779047760374082784198656)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            5316993112778078098296924030126522368)
                          (Code.joinWords 128
                            18014398509481984
                            4951779046625466976686833664))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            37778931871753254731776
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            5316911983139663491615228241121378304)
                          (Code.joinWords 128
                            18014398509481984
                            37926523829945347604480)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            332312069548629881143557751882907648
                            5316993112778078098296924030126522368)
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984))
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          69324642199981295394350956544
                          (Nat.shiftLeft
                            316356262996809977751106080346722009088
                            128))
                        (Code.joinWords 128
                          9903520314346092593990860800
                          65865144552521728))
                      (Code.joinWords 512
                        4951760157141521099596496896
                        (Code.joinWords 128
                          4951760157159535772988080192
                          274877906944)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        32768
                        2361183241434822606848)
                      (Code.joinWords 512
                        4951760157141521099596496896
                        1180591620717411303424))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1024
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            18014673387388992
                            274877907008)
                          (Nat.shiftLeft
                            1024
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          27021597764222976
                          9570149208293376)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          18014673387388992
                          274877906944)
                        512)))
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        297747071055821155530452781502797185024
                        311039351013670314259490852105600630784)
                      256)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        298577838553186727951017660915472400384
                        311922041479621234956341036481568047104)
                      256))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13835058055282163712
                            1237940053985129458636423168)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
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
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            1152921504606846976
                            1237940040438301779505971200))))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            549755813888
                            1237940039285380859014676480)))
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
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
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
                            1152921504606846976
                            4951760158294442604203343872)))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          13835058055282163712
                          14699749183737298944)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976))
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            59421121885698253195157962752
                            618970019642690137449562112)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            59653235643064261996701548544
                            618970019642690137449562112)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4951779046607452578177351680
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            4951779046607452578177351680
                            128))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            37778931862957161709568
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            549755813888
                            37926505816130953674752)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        512))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      512)
                    1024)
                  2048)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          301989888
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          131072
                          128)
                        (Nat.shiftLeft
                          33685504
                          128)))
                    1024)
                  2048))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            906694364710971881029632
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            910236139573124114939904
                            128)
                          256))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            4951760158294442604203343872
                            128))
                        (Code.joinWords 256
                          830777638570374246400091386300858368
                          (Code.joinWords 128
                            2361183241434822606848
                            4951760157159535498105978880)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            9903520314283042199192993792
                            37778931871753254731776))
                        (Code.joinWords 256
                          830767497365572420564879412675215360
                          (Code.joinWords 128
                            9942205940510710332783591424
                            37926523829945347604480)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          9903520314283042199192993792
                          256)
                        (Code.joinWords 256
                          830777638570374246400091386300858368
                          (Code.joinWords 128
                            9942205940510710332783591424
                            18014398509481984)))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
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
                          311926108736572067230375738653802496000
                          128)
                        256))
                    1024)
                  2048)
                (Nat.shiftLeft
                  (Code.joinWords 512
                    32768
                    (Nat.shiftLeft
                      128
                      256))
                  1024))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            619876714007401109330591744
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            619880255782263261564502016
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            906694364710971881029632
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1061351867024952761778176
                            128)
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128))
                        (Code.joinWords 256
                          830777638570374246400091386300858368
                          (Nat.shiftLeft
                            4951760158294442604203343872
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9903520314283042199192993792
                            14411518807585587200)
                          256)
                        (Nat.shiftLeft
                          9942205940510710332783591424
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          9903520314283042199192993792
                          256)
                        (Code.joinWords 256
                          830777638570374246400091386300858368
                          (Code.joinWords 128
                            9942205940510710332783591424
                            1152921504606846976)))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128))
                        (Code.joinWords 256
                          830777638570374246400091386300858368
                          (Code.joinWords 128
                            2361183241434822606848
                            4951760157141521099596496896)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9903520314283042199192993792
                            37778931862957161709568)
                          256)
                        (Code.joinWords 256
                          830767497365572420564879412675215360
                          (Code.joinWords 128
                            9942205940510710332783591424
                            37926505816130953674752)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          664613997892457936451903530140172288
                          9903520314283042199192993792)
                        (Code.joinWords 256
                          830777638570374246400091386300858368
                          9942357056238162161430429696))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    32768
                    (Code.joinWords 512
                      (Code.joinWords 256
                        268435456
                        (Code.joinWords 128
                          268435456
                          268435456))
                      (Nat.shiftLeft
                        268435456
                        256)))
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            1237940039285389070992146432
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2361201255833332088832
                            1237940039303394673408606208)
                          256))
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
                          256)))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1170935903116328960
                            128)
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          59421121885698253195157962752
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Code.joinWords 128
                            59653235643082276395211030528
                            18014398509481984)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            4951760158294442604203343872)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014398509481984
                            4951760157159535498105978880)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            37778931871753254731776
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014398509481984
                            37926523829945347604480)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984)
                          256)
                        512))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1024
                        128)
                      256)
                    (Nat.shiftLeft
                      64
                      256))
                  1024)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13835058055282163712
                            1237940053985129458636423168)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            131072
                            128)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760157141521099596496896
                            1237940039285380274899124224)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760158294442604203343872
                            1237940040438301779505971200)
                          256)))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6189700196426901374495621120
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2361183241984578420736
                            1237940039285380859014676480)
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
                (Code.joinWords 4096
                  (Code.joinWords 2048
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
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          13835058055282163712
                          14735777980756262912)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          59421121885698253195157962752
                          256)
                        (Nat.shiftLeft
                          62129115721635022546499796992
                          256))
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
                          256)))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          37778931863506917523456
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          37778931863506917523456
                          37926505816130953674752)
                        256)))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (1664 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage026
