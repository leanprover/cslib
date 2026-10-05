/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 513–576 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage008

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            317571260521360363059246478484461060096)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            317191178246939496938272656972285214720
                            317575413978552921089020055556628414464)
                          256)
                        512))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            314528574502605718440563094822573834240
                            864691128455135232)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          6147689621710037738303550003573948416
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          6147679480505235912468338029948305408
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          6480077750294681313211197557649178624
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1163089708119004127543649138183766016
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1163074496582600772384508112879484928
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1163089708389803511137326073317949440
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1163074496311801389079061553897013248
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1163089708119004127831879514335477760
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1163074496582600772384508112879484928
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1163089708389803511137326073317949440
                          256)
                        512)))))
              16384)
            32768)
          65536)
        (Code.joinWords 65536
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          338509197543748819842931192119076847616
                          128)
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          244022740543934159801343866306560
                          128)
                        256)
                      512)
                    1024))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2699995000263410481094674027621908480
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          41539008693578735142944718985363456
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2699994366438110366982225079083991040
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2699995000263410481096925827435593728
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          41539008693578735145196518799048704
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51923602410648390402257511457488896
                          256)
                        512)))))
              16384)
            32768)
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        81129638414606681695789005144064
                        256)
                      512)
                    1024)
                  2048)
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      63969097297149076383783945152143294464
                      256)
                    512)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        81129638414606681695789005144064
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        81129638414606681695789005144064
                        256)
                      512))))
              16384)
            32768)))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          333524592619208620947906428455989805056
                          128)
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          15845632506542216333450700390400
                          128)
                        256)
                      512)
                    1024))
                8192)
              16384)
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          207692508205378845483588735111004160
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          207691874389750137925805020157050880
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          207692508215050252040505768508653568
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          41539008693578735142944718985363456
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          41539008703250141699861752383012864
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51923602420319796956922745041453056
                          128)
                        256))))
                8192)
              16384))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            15211807202738752817960438464512
                            15845632502852867518708790067200)
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          128)
                        (Code.joinWords 128
                          170141183460469231731687303715884105728
                          338506601395319552414417177687174938624))
                      512)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          40564819207303340847894502572032
                          128)
                        (Code.joinWords 128
                          2535301200456458802993406410752
                          43100120407759799650887908982784))
                      512)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            320182671463854524755505746955663835136
                            333527077848210368391648062742623944704)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            15211807202738752817960438464512
                            15845632506542216333450700390400)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2535301200456458802993406410752
                          2535301200456458802993406410752)
                        256)
                      512))))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5316993112778078098296924030126522368
                        256)
                      (Nat.shiftLeft
                        5316993112778078098296924030126522368
                        256)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166153499473114484112975882535043072
                          207691874351064511698136886566453248)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166478018026772910839759038555619328
                            218401620447092707796681783597072384)
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        48018361347730085908938260428779159552
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            51964325695852128826445826631925760
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Nat.shiftLeft
                            40723275532331869523081590472704
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316911983139663491615228241121378304
                            51923760876644825485597932129353728)
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5483146612251192582409899912661565440
                            218077101922448500740649727769444352)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166153499473114484112975882535043072
                          207691874389750137925805020157050880)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5483471130804851009136683068682141696
                          218401620485778334024349917187670016)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5317317631331736525023707186147098624
                            51923760866973418928680898731704320)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5316993112778078098296924030126522368
                          51923760876644825485597932129353728)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5316993112778078098296924030126522368
                          51923760876644825485597932129353728)
                        256))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            63807811575980838300284486233765183488
                            128)
                          (Nat.shiftLeft
                            5040812611807554215051640296177664
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            15845632502852867518708790067200
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            244022740543934159788115367034880
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          43100120407759799650887908982784
                          128)
                        (Nat.shiftLeft
                          43100120407759799650887908982784
                          128))
                      512)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            335293583760366676695877997821952
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            15845632506542216333450700390400
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          2535301200456458802993406410752
                          128)
                        (Code.joinWords 128
                          2535301200456458802993406410752
                          2535301200456458802993406410752))
                      512))))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)
                        256)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10428486119102557700087816006926336
                            158456325028528675187087900672)
                          256)
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          256))
                      (Nat.shiftLeft
                        10385385998694797900436928097943552
                        256))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            487411655787754204875482382467072
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            244022740543934159801343866306560
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          40564819207303340847894502572032
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          40564819207303340847894502572032
                          128)
                        (Nat.shiftLeft
                          40564819207303340847894502572032
                          128)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2834994084760015885177650995754172416
                            176538093228869765597705008784080896)
                          256)
                        (Nat.shiftLeft
                          2668840585286901401208790301294985216
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166153499473114484112975882535043072
                          166153499511800110340644016125640704)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          176862611743842566096820031214059520
                          176862611782528192324488164804657152)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256)
                        (Nat.shiftLeft
                          2658455991569831745951729308636545024
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2669165103840559827791458269239705600
                          256)
                        (Nat.shiftLeft
                          2669165103840559827935573457315561472
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10384752173394683785736179746340864
                            158456325028528675187087900672)
                          256)
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          256))
                      (Nat.shiftLeft
                        10384752173394683785736179746340864
                        256)))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            335293583760366676695877997821952))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            15211807202738752817960438464512
                            15845632502852867518708790067200))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        63969097297149076383495714775991582720
                        63969097297149076383495714775991582720)
                      512)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          43100120407759799650887908982784
                          128)
                        (Code.joinWords 128
                          2535301200456458802993406410752
                          43100120407759799650887908982784))
                      512)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            334659758460252561995129646219264
                            340364186161279594301864810643456))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            15211807202738752817960438464512
                            15845632506542216333450700390400)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          2535301200456458802993406410752
                          128)
                        (Code.joinWords 128
                          2535301200456458802993406410752
                          2693757525484987478180494311424))
                      512))))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)
                        256)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        2693757525484987478180494311424
                        158456325028528675187087900672)
                      256))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166153499473114484112975882535043072
                          166153499473114484112975882535043072)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            176943741382257172778515820219203584
                            176862611743842566096820031214059520)
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        63969097297149076383495714775991582720
                        63969097297149076383495714775991582720)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            81129638414606681695789005144064
                            40723275532331869523081590472704)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Code.joinWords 128
                            81129638414606681695789005144064
                            40723275532331869523081590472704)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            176538093190184139370036875193483264
                            176862611782528192324488164804657152)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166153499473114484112975882535043072
                          176538093228869765597705008784080896)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          176862611743842566096820031214059520
                          176862611782528192324488164804657152)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        158456325028528675187087900672
                        158456325028528675187087900672)
                      256)))))))))
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            312036272070162236807232969397512437760
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            232113757366008801543585792
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          13624749216149588163082750213065015296
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
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
                            312206497203710048721119290694041600000
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            317575413918898775224516193919921291264
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          13624586956872758949719358635054727168
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18941666269891652567615584440999215104
                          128)
                        256))))
                8192)
              16384)
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18609435329904066040698386210940256256
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18609191941066193473108635111106019328
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18609435329981437293153722478121451520
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18609191940988822221662105160455815168
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18609435329904066041707192527471247360
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18609191940988822221662105160455815168
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18609435329904066041707192527471247360
                          128)
                        256))))
                8192)
              16384))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            5070602400912917605986812821504
                            128)
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        42535295865117307932921825928971026432
                        45526058855710739899410728081782996992)
                      256)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          128)
                        256)
                      1024))))
              16384)
            (Nat.shiftLeft
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        81129638414606681695789005144064
                        256)
                      512)
                    1024)
                  2048)
                (Code.joinWords 2048
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      42535295865117307932921825928971026432
                      256)
                    (Nat.shiftLeft
                      48018361347730085908938260428779159552
                      256))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        81129638414606681695789005144064
                        256)
                      512)
                    1024)))
              16384)))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          128)
                        (Nat.shiftLeft
                          333521996411126117891027901211123646464
                          128)))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            243388915243820045087367015432192
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            244022740543934159788115367034880
                            128)
                          256))
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          40564819207303340847894502572032
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          2535301200456458802993406410752
                          128)
                        (Nat.shiftLeft
                          43100120407759799650887908982784
                          128)))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        45526058855710739899410728081782996992
                        128)
                      256)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256)
                        (Nat.shiftLeft
                          2699994366438110366838109891008135168
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2658780510123490172534397276581265408
                            5070602400912917605986812821504)
                          256)
                        (Nat.shiftLeft
                          2710704112534138562936654788038754304
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            51926296168173875389735691951800320
                            2693757525484987478180494311424))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            5070602400912917605986812821504)
                          256)
                        (Nat.shiftLeft
                          51923760866973418930932698545389568
                          256))))))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        332312069548629881143557751882907648
                        256)
                      (Nat.shiftLeft
                        332312069548629881143557751882907648
                        256))
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            337628940966950337346531881413263753216
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338511644743232560439790781504614825984
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            243388915243820045087367015432192
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            244022740543934159801343866306560
                            128)
                          256))
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          40564819207303340847894502572032
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          40564819207303340847894502572032
                          128)
                        256))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2990768061118461626951171872443596800
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          2710379593980480136351735020280348672
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332636588102288307870340907903483904
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          51923760866973418928680898731704320
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256)
                        (Nat.shiftLeft
                          2699994366438110366982225079083991040
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2991092579672120053677955028464173056
                          256)
                        (Nat.shiftLeft
                          2710704112534138563080769976114610176
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256)
                        (Nat.shiftLeft
                          51923760866973418930932698545389568
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256)
                        (Nat.shiftLeft
                          51923760866973418930932698545389568
                          256))))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            298743992052659842435130636798007443456
                            312077810385377279785196951371444649984)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            319014718988379809496913694467282698240
                            319014718988379809496913694467282698240)
                          (Code.joinWords 128
                            320177793484691610885704525645027999744
                            333521996411126117891027901211123646464)))
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        63802943797675961899382738893456539648
                        256)
                      (Nat.shiftLeft
                        63969097297149076383495714775991582720
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332388128584643574907647554075230208
                            40564819207303340847894502572032)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            83664939615063140498782411554816
                            43258576732788328326074996883456)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332393199187044487825253540888051712
                            5070602400912917605986812821504)
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          332306998946228968225951765070086144
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          42867602864063536901147777694041112576
                          66793706788269393865871641046268510208)
                        256)
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332636588102288307870340907903483904
                            5070602400912917605986812821504)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            5070602400912917605986812821504)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            2693757525484987478180494311424
                            2693757525484987478180494311424)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070602400912917605986812821504)
                        256)))))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        332312069548629881143557751882907648
                        256)
                      (Nat.shiftLeft
                        332312069548629881143557751882907648
                        256))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        332312069548629881143557751882907648
                        256)
                      (Nat.shiftLeft
                        332312069548629881143557751882907648
                        256))
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332717717740702914552036696908627968
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        63802943797675961899382738893456539648
                        256)
                      (Nat.shiftLeft
                        63969097297149076383783945152143294464
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332393199187044487825253540888051712
                            40723275532331869523081590472704)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            81129638414606681695789005144064
                            40723275532331869523081590472704)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          332393199187044487825253540888051712
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332636588102288307870340907903483904
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332636588102288307870340907903483904
                          324518553658426726783156020576256)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          332636588102288307870340907903483904
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        332312069548629881143557751882907648
                        256)
                      (Nat.shiftLeft
                        332312069548629881143557751882907648
                        256)))))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      66461399789323164897645689281198424064
                      128)
                    256)
                  2048)
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        5070602400912917605986812821504
                        128)
                      256)
                    1024)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        5070602400912917605986812821504
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        5070602400912917605986812821504
                        128)
                      256))))
              8192)
            16384)
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5316993112778078098296924030126522368
                        256)
                      (Nat.shiftLeft
                        5316993112778078098296924030126522368
                        256))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        63802943797675961899382738893456539648
                        66461399789245793645190353014017228800)
                      256)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319014718988379809496913694467282698240
                            128)
                          (Code.joinWords 128
                            313697807005240146005298466226161319936
                            337623910929368631717566993311207522304))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319014718988379809496913694467282698240
                            128)
                          (Code.joinWords 128
                            314570112877473997046891589609470296064
                            338506601395319552414417177687174938624)))
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316917053742064404532834227934199808
                            45635421608216258453881315393536)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            43258576732788328326074996883456)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316998183380479011214530016939343872
                            5070602400912917605986812821504)
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        63802943797675961899382738893456539648
                        66461399789323164897645689281198424064)
                      256))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5317322701934137437941313172959920128
                            5070602400912917605986812821504)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316998183380479011214530016939343872
                            5070602400912917605986812821504)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2693757525484987478180494311424
                            2693757525484987478180494311424)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5316998183380479011214530016939343872
                          5070602400912917605986812821504)
                        256))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5316993112778078098296924030126522368
                        256)
                      (Nat.shiftLeft
                        5316993112778078098296924030126522368
                        256)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5316911983139663491615228241121378304
                          324518553658426726783156020576256)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5317317631331736525023707186147098624
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          47852207848256971424537054170092404736
                          256)
                        (Nat.shiftLeft
                          69286009280288739875399173393264672768
                          256))
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316911983139663491615228241121378304
                            40723275532331869523081590472704)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Code.joinWords 128
                            81129638414606681695789005144064
                            40723275532331869523081590472704)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5317317631331736525023707186147098624
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5317317631331736525023707186147098624
                          324518553658426726783156020576256)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5317317631331736525023707186147098624
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5316993112778078098296924030126522368
                        256)
                      (Nat.shiftLeft
                        5316993112778078098296924030126522368
                        256))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5070602400912917605986812821504)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5070602400912917605986812821504)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5070602400912917605986812821504)
                        256)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            162259276829213363391578010288128
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            487411655787754204875482382467072
                            128)))
                      1024)
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        66461399789245793645190353014017228800
                        128)
                      (Nat.shiftLeft
                        66461399789245793645190353014017228800
                        128)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            243388915243820045087367015432192
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            244022740543934159788115367034880
                            128)))
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          40564819207303340847894502572032
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          43100120407759799650887908982784
                          128)
                        (Nat.shiftLeft
                          43100120407759799650887908982784
                          128)))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        66461399789245793645190353014017228800
                        128)
                      (Nat.shiftLeft
                        66461399789245793645190353014017228800
                        128))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256)
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2669170174442960740709064256052527104
                            5070602400912917605986812821504)
                          256)
                        (Nat.shiftLeft
                          2669165103840559827791458269239705600
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            5070602400912917605986812821504)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            2693757525484987478180494311424
                            2693757525484987478180494311424)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5070602400912917605986812821504)
                        256))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)
                        256)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256))
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        40723275532331869523081590472704
                        256)
                      (Nat.shiftLeft
                        158456325028528675187087900672
                        256))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            486777830487640090174734030864384
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            568541294202360886571271387611136
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            243388915243820045087367015432192
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            244022740543934159801343866306560
                            128)
                          256))
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          40564819207303340847894502572032
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          40564819207303340847894502572032
                          128)
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          128)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2668840585286901401064675113219129344
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          2669165103840559827935573457315561472
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256)
                        (Nat.shiftLeft
                          2668840585286901401208790301294985216
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2669165103840559827791458269239705600
                          256)
                        (Nat.shiftLeft
                          2669165103840559827935573457315561472
                          256)))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        158456325028528675187087900672
                        256)
                      (Nat.shiftLeft
                        158456325028528675187087900672
                        256)))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5070602400912917605986812821504)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5070602400912917605986812821504)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5070602400912917605986812821504)
                        256)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        66461399789245793645190353014017228800
                        128)
                      (Code.joinWords 128
                        63802943797675961899382738893456539648
                        66461399789245793645190353014017228800))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        63802943797675961899382738893456539648
                        256)
                      (Code.joinWords 256
                        63969097297149076383495714775991582720
                        63969097297149076383495714775991582720))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            86200240815519599301775817965568
                            45635421608216258453881315393536)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            43100120407759799650887908982784
                            128)
                          (Code.joinWords 128
                            83664939615063140498782411554816
                            43258576732788328326074996883456)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            86200240815519599301775817965568
                            5070602400912917605986812821504)
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)
                        512)
                      1024)
                    (Code.joinWords 256
                      (Nat.shiftLeft
                        66461399789245793645190353014017228800
                        128)
                      (Code.joinWords 128
                        63802943797675961899382738893456539648
                        66461399789245793645190353014017228800)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            329589156059339644389142833397760
                            5070602400912917605986812821504)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            5070602400912917605986812821504)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            2693757525484987478180494311424
                            2693757525484987478180494311424)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5070602400912917605986812821504
                          5070602400912917605986812821504)
                        256))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        256)
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        256))
                    1024)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            405648192073033408478945025720320
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        63802943797675961899382738893456539648
                        256)
                      (Code.joinWords 256
                        63969097297149076383495714775991582720
                        63969097297149076383495714775991582720))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            81129638414606681695789005144064
                            40723275532331869523081590472704)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Code.joinWords 128
                            81129638414606681695789005144064
                            40723275532331869523081590472704)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          324518553658426726783156020576256
                          324518553658426726783156020576256)
                        256)
                      1024))
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        256)
                      (Nat.shiftLeft
                        324518553658426726783156020576256
                        256))
                    1024)))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (512 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage008
