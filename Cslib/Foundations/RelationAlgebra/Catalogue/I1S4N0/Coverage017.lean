/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1089–1152 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage017

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            311926108736572067230375738653802496000)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            312258420806120697111519296405685403648
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            312258420806120697111519296405685403648)
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4344936211666724279313632264
                          128)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319845486485745381917478573879957913600
                          333189689412179888922801949446053560320)
                        256)
                      512))
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
                        (Code.joinWords 128
                          212679075474015807078423394893019742208
                          332312069548629881143557751882907648)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Nat.shiftLeft
                            910236139573398992846848
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          213343689471908265014875298423159914496
                          332312069548629881143557751882907648)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319849390849594084864035183725830471680
                          332312069548629881143557751882907648)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          319014718988379809496913694467282698240
                          (Code.joinWords 128
                            4951760158294442604203343872
                            1152921504606846976))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            319849390849594084864035183725830471680
                            332312069548629881143557751882907648)
                          4951760157141521099596496896)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319849390849594084864035183725830471680
                          332312069548629881143557751882907648)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            319845486485745381917478573879957913600
                            332312069548629881143557751882907648)
                          (Code.joinWords 128
                            4951760157141521099596496896
                            274877906944))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            319849390849594084864035183725830471680
                            332312069548629881143557751882907648)
                          4951760157141521099596496896)
                        512))))))
            32768)
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984))
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
                            332312069548629881143557751882907648
                            128)
                          (Code.joinWords 128
                            18014398509481984
                            18014398509481984))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332312069548629881143557751882907648)
                          (Code.joinWords 128
                            18014398509481984
                            18014673387388928))
                        512)
                      1024))
                  4096))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        298577838553186727951017660915472400384
                        311922041479621234956341036481568047104)
                      256))
                  2048)
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        212676479325586539664609129644855132160
                        225968759283435698393647200247658577920)
                      256)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        319845486485745381917478573879957913600
                        333189689412179888922801949446053560320)
                      256))
                  2048))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
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
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          332312069548629881143557751882907648)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332312069548629881143557751882907648)
                          (Code.joinWords 128
                            274877906944
                            274877906944))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          332312069548629881143557751882907648)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          332312069548629881143557751882907648)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            9223372036854775808
                            12105675798371893248)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          332312069548629881143557751882907648)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          332312069548629881143557751882907648)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332312069548629881143557751882907648)
                          (Code.joinWords 128
                            274877906944
                            274877906944))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          332312069548629881143557751882907648)
                        512))))))))
        131072)
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            311926108736572067230375738653802496000
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            317243101849350145328672662683929018368
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            225971517691141795020824857073833476096
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            317243101849350145328672662683929018368
                            128)
                          256))))
                  4096)
                8192)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          212679075474015807078423394893019742208
                          128)
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            18889466155778952921088
                            128))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          223312899440295134061653851375262498816
                          128)
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128))))
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65866003544408264
                          128)
                        512)
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
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        332306998946228968225951765070086144000
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        333189689412179888922801949446053560320
                        128)
                      256)))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          332311055428149698560036554520343347200
                          128)
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          332311055428149698560036554520343347200
                          128)
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319014718988379809496913694467282698240
                            128)
                          (Nat.shiftLeft
                            4951760158294442604203343872
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4951760157141521099596496896
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332311055428149698560036554520343347200
                            128)
                          (Nat.shiftLeft
                            1152921504606846976
                            128))
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144000
                            128)
                          (Nat.shiftLeft
                            1152921504606846976
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332311055428149698560036554520343347200
                            128)
                          (Nat.shiftLeft
                            1152921504606846976
                            128))
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)))))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          807403520
                          2228224)
                        (Code.joinWords 128
                          807403520
                          841089024))
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        298577838553186727951017660915472400384
                        311924637628050502370155301729732657152)
                      256)
                    512)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18226054497828864
                            18239282997100544)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014673387388928
                            18014673387388928)
                          256)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
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
                            18014673387388928
                            18014673387388928)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18226054497828864
                            18889484170761577955328)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014673387388928
                            18014673387388928)
                          256)
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          63050394797867008
                          65865144552521728)
                        512)
                      (Code.joinWords 512
                        16384
                        (Code.joinWords 128
                          18014673391583296
                          274877906944)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      16384
                      16384)
                    2048))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      16384
                      (Code.joinWords 128
                        18014673387388992
                        274877907008))
                    1024)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        27021597764222976
                        9570149208293376)
                      512)
                    (Code.joinWords 512
                      16384
                      (Code.joinWords 128
                        18014673387388992
                        274877906944)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            16140901064495857664
                            17149707381026848768)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976)
                          256))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          16384
                          5316993112778078098296924030126522368)
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            16384
                            5316911983139663491615228241121378304)
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            274877906944
                            18889465931753458761728)
                          256))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          16384
                          5316993112778078098296924030126522368)
                        (Code.joinWords 128
                          1152921504606846976
                          1224979098644774912)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          16384
                          5316993112778078098296924030126522368)
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            16140901064495857664
                            17149707381026848768)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976)
                          256))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          16384
                          5316993112778078098296924030126522368)
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            4951760158294442604203343872)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760157141521099596496896
                            4951760157141521099596496896)
                          256))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          16384
                          5316993112778078098296924030126522368)
                        (Code.joinWords 128
                          1152921504606846976
                          1224979098644774912)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            16384
                            5316911983139663491615228241121378304)
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            274877906944
                            18889465931753458761728)
                          256))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          16384
                          6646221108562993971200731090406866944)
                        (Code.joinWords 128
                          1152921504606846976
                          1224979098644774912)))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
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
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        298910145552132956919243612680542486528
                        312254348478567463924566988246638133248)
                      256)
                    512)
                  4096))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Code.joinWords 128
                            59653235643082276395211030528
                            18014398509481984))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            18014398509481984
                            18014673387388928))
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Code.joinWords 128
                            18014398509481984
                            18889484170761577955328))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          (Code.joinWords 128
                            18014398509481984
                            18014673387388928))
                        512)))
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        316356262996809977751106080346722009088
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        317238953462760898447956264722689425408
                        128)
                      256))
                  2048)
                (Nat.shiftLeft
                  16384
                  1024))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Nat.shiftLeft
                            1237940053985129458636423168
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237958928751311753479979008
                            128)
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1238888201930769220730093568
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237958928751311753479979008
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            16384
                            5316993112778078098296924030126522368)
                          (Nat.shiftLeft
                            1152921504606846976
                            128))
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          4951760157141521099596496896))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Nat.shiftLeft
                            17149707381026848768
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760158294442604203343872
                            1152921504606846976)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            16384
                            5316993112778078098296924030126522368)
                          (Nat.shiftLeft
                            1152921504606846976
                            128))
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          4951760157141521099596496896))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4951760158294442604203343872
                            128)
                          256)
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Code.joinWords 128
                            69595441583574972329485139968
                            4951760157141521099596496896)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            16384
                            5316993112778078098296924030126522368)
                          (Nat.shiftLeft
                            1152921504606846976
                            128))
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          4951760157141521099596496896)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Nat.shiftLeft
                            1152921504606846976
                            128))
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Code.joinWords 128
                            4951760157141521099596496896
                            18889465931753458761728)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            1152921504606846976
                            128))
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          4951760157141521099596496896))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
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
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        298912751841767026158893089902332739584
                        312257117661303662491694557794790277120)
                      256)
                    512)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18226054497828864
                            18239282997100544)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014673387388928
                            18014673387388928)
                          256)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18155135997837312
                            18164481846673408)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014673387388928
                            18014673387388928)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18226054497828864
                            18889484170761577955328)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            18014673387388928
                            18014673387388928)
                          256)
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  16384
                  1024)
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
                            16140901064495857664
                            17149707381026848768))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976)
                          256))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          16384
                          6646221108562993971200731090406866944)
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            16384
                            5316911983139663491615228241121378304)
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            274877906944
                            18889465931753458761728)
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          6646221108562993971200731090406866944
                          128)
                        (Code.joinWords 128
                          1152921504606846976
                          1224979098644774912)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          16384
                          6646221108562993971200731090406866944)
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            16140901064495857664
                            17149707381026848768))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976)
                          256))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          16384
                          6646221108562993971200731090406866944)
                        (Code.joinWords 128
                          1152921504606846976
                          1224979098644774912))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1152921504606846976
                            4951760158294442604203343872)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760157141521099596496896
                            4951760157141521099596496896)
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          6646221108562993971200731090406866944
                          128)
                        (Code.joinWords 128
                          1152921504606846976
                          1224979098644774912)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Code.joinWords 128
                            1152921504606846976
                            1152921504606846976))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            274877906944
                            18889465931753458761728)
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          6646221108562993971200731090406866944
                          128)
                        (Code.joinWords 128
                          1152921504606846976
                          1224979098644774912)))))))))))
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          838860800
                          128)
                        (Nat.shiftLeft
                          838860800
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          33685504
                          128)
                        (Nat.shiftLeft
                          841089024
                          128)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          4332790137498830962381815808
                          128)
                        (Nat.shiftLeft
                          4344879395694977253927682048
                          128))
                      (Code.joinWords 512
                        (Code.joinWords 128
                          16384
                          1237958928751311753547088896)
                        (Nat.shiftLeft
                          18889465931478580854784
                          128)))
                    (Code.joinWords 1024
                      16384
                      16384))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1238884512581954203941863424
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1238888201930768945852186624
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
                            1237958928751311753479979008
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
                            69324642199981295394350956544
                            4951760157141521099596496896)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            69595441583574972329485139968
                            4951760157141521099596496896)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          4951760157141521099596496896)
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          4951760157141521099596496896)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Code.joinWords 128
                            4951760157141521099596496896
                            18889465931478580854784))
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Code.joinWords 128
                            4951760157141521099596496896
                            18889465931753458761728)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          4951760157141521099596496896)
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          4971102970255355166391795712))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        311039351013670314259490852105600630784
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        311924637628050502370155301729732657152
                        128)
                      256))
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 128
                        16384
                        1237958928751311753479980032)
                      (Nat.shiftLeft
                        18889465931478580855808
                        128))
                    1024)
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        1856910058928070412348686336
                        128)
                      (Nat.shiftLeft
                        621387871281919395799105536
                        128))
                    (Code.joinWords 512
                      (Code.joinWords 128
                        16384
                        1237958928751311753479980032)
                      (Nat.shiftLeft
                        18889465931478580854784
                        128)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
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
                            1237958928751311753479979008
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1237958928751311753479979008
                            128)
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1238884512581954203941863424
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1238888201930769220730093568
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
                            1237958928751311753479979008
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          4951760157141521099596496896)
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          4951760157141521099596496896))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760157141521099596496896
                            1152921504606846976)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760158294442604203343872
                            1152921504606846976)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          4951760157141521099596496896)
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          4971102970255355166391795712))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            69324642199981295394350956544
                            4951760157141521099596496896)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            69595441583574972329485139968
                            4951760157141521099596496896)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          4951760157141521099596496896)
                        (Code.joinWords 256
                          332312069548629881143557751882907648
                          4951760157141521099596496896)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Code.joinWords 128
                            4951760157141521099596496896
                            18889465931478580854784))
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Code.joinWords 128
                            4951760157141521099596496896
                            18889465931753458761728)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          4951760157141521099596496896)
                        (Code.joinWords 256
                          415388819285187123200045693150429184
                          4971102970255355166391795712))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Code.joinWords 128
                          268451840
                          268435456)
                        (Code.joinWords 128
                          268435456
                          268435456))
                      (Nat.shiftLeft
                        268435456
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    16384
                    2048)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          18889465931478580854784
                          128))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          274877906944
                          18889465931753458761728)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760157141521099596496896
                          4951760157141521099596496896)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760157141521099596496896
                          4951760157141521099596496896)
                        256))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          18889465931478580854784
                          128))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          274877906944
                          18963252908048296968192)
                        256)))
                  4096)))
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          18889465931478580854784
                          128))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          274877906944
                          18889465931770638630912)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
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
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760157141521099596496896
                          4951760157141521099596496896)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760157141521099596496896
                          4951760157141521099596496896)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18889465931478580854784
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          274877906944
                          18963252908065476837376)
                        256)))))
              16384)))
        131072)
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        311039351013670314259490852105600630784
                        128)
                      256)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        170141183460469231731687303715884105728
                        311922041479621234956341036481568047104)
                      256))
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
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
                            128)))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
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
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Nat.shiftLeft
                            18889465931478580854784
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128))))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        212676479325586539664609129644855132160
                        332306998946228968225951765070086144000)
                      256)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        213507246822952112085174009057530347520
                        333189689412179888922801949446053560320)
                      256))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
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
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Nat.shiftLeft
                            1237940039285380274899124224
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            1237958928751311753479979008
                            128)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            39614081257132168796771975168
                            4951760157141521099596496896)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            49672344076325883530327359488
                            4951760157141521099596496896)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316911983139663491615228241121378304
                            128)
                          (Nat.shiftLeft
                            18889465931478580854784
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            5316993112778078098296924030126522368
                            128)
                          (Nat.shiftLeft
                            18889465931478580854784
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128)
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          128))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Code.joinWords 256
                      268451840
                      (Code.joinWords 128
                        268435456
                        268435456))
                    (Code.joinWords 256
                      268435456
                      268435456))
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          18889465931478580854784
                          128))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          274877906944
                          18889465931753458761728)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760157141521099596496896
                          4951760157141521099596496896)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760157141521099596496896
                          4951760157141521099596496896)
                        256))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          18889465931478580854784
                          128))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          274877906944
                          18963252908048296968192)
                        256)))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  16384
                  2048)
                4096)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          18889465931478580854784
                          128))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          274877906944
                          18889465931770638630912)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
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
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760157141521099596496896
                          4951760157141521099596496896)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760157141521099596496896
                          4951760157141521099596496896)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18889465931478580854784
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          274877906944
                          18963252908065476837376)
                        256))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
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
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1238884512581954203941863424
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1238888201930768945852186624
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
                            1237958928751311753479979008
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
                            69324642199981295394350956544
                            4951760157141521099596496896)
                          256)
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Code.joinWords 128
                            69595441583574972329485139968
                            4951760157141521099596496896)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          4951760157141521099596496896)
                        (Code.joinWords 256
                          415388819285187123200045693150429184
                          4951760157141521099596496896)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          (Code.joinWords 128
                            4951760157141521099596496896
                            18889465931478580854784))
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Code.joinWords 128
                            4951760157141521099596496896
                            18889465931753458761728)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          256)
                        (Code.joinWords 256
                          415388819285187123200045693150429184
                          4971102970255355166391795712))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        316359021404516074378283737172896907264
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        317241722645497097015083834270841569280
                        128)
                      256))
                  2048)
                (Nat.shiftLeft
                  16384
                  1024))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1238544502195187589486477312
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1238584642310291981470793728
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
                            1237958928751311753479979008
                            128)
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1238884512581954203941863424
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1238888201930769220730093568
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
                            1237958928751311753479979008
                            128)
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          4951760157141521099596496896)
                        (Code.joinWords 256
                          415388819285187123200045693150429184
                          4951760157141521099596496896))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760157141521099596496896
                            1152921504606846976)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760158294442604203343872
                            1152921504606846976)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          256)
                        (Code.joinWords 256
                          415388819285187123200045693150429184
                          4971102970255355166391795712))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            69324642199981295394350956544
                            4951760157141521099596496896)
                          256)
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Code.joinWords 128
                            69595441583574972329485139968
                            4951760157141521099596496896)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          16384
                          4951760157141521099596496896)
                        (Code.joinWords 256
                          415388819285187123200045693150429184
                          4971102970255355166391795712)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4951760157141521099596496896
                            18889465931478580854784)
                          256)
                        (Code.joinWords 256
                          332306998946228968225951765070086144
                          (Code.joinWords 128
                            4951760157141521099596496896
                            18889465931753458761728)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          4951760157141521099596496896
                          256)
                        (Code.joinWords 256
                          415388819285187123200045693150429184
                          4971102970255355166391795712))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Code.joinWords 256
                      268451840
                      (Code.joinWords 128
                        268435456
                        268435456))
                    (Nat.shiftLeft
                      268435456
                      256))
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          18889465931478580854784
                          128))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          274877906944
                          18889465931753458761728)
                        256))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760157141521099596496896
                          4951760157141521099596496896)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760157141521099596496896
                          4951760157141521099596496896)
                        256))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          18889465931478580854784
                          128))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          274877906944
                          18963252908065476837376)
                        256)))
                  4096)))
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        16384
                        (Nat.shiftLeft
                          18889465931478580854784
                          128))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          274877906944
                          18963252908065476837376)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4951760158294442604203343872
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760158294442604203343872
                          4951760158294442604203343872)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1152921504606846976
                          1152921504606846976)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760157141521099596496896
                          4951760157141521099596496896)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4951760157141521099596496896
                          4951760157141521099596496896)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18889465931478580854784
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          274877906944
                          18963252908065476837376)
                        256)))))
              16384))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (1088 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage017
