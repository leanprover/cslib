/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 449–512 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage007

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            604462909807314587353088
                            170141183460469231731687303715884105728)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            604462909807314587353088
                            170141183460469231731687303715884105728)
                          256)
                        512))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            39614081257132168796771975168
                            170141183460469231731687303715884105728)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            39614081257132168796771975168
                            170141183460469231731687303715884105728)
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            32768
                            170141183460469231731687303715884138496)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            32768
                            170141183460469231731687303715884138496)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            604462909807314587353088
                            170141183460469231731687303715884105728)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            604462909807314587353088
                            170141183460469231731687303715884105728)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256)
                        512)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            317243101849350145328672662683929018368
                            317243101849350145328672662683929018368)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          128768962091663725187556308964658380800
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          384235671959278271543563463526711296
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2710378960155180022092919083852890112
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          52004732049062997081701500648947712
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          384229967531577244511256728362287104
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            59479150325039755395543859200
                            271162511140180866511718142497576386560)
                          51928673013049303317611698456625152)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51923602410648390400005711643803648
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51923602410648390400005711643803648
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51923602410648390400005711643803648
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            272159432136961524977054495592400551936
                            272221739699263942908596861548351389696)
                          51923602410648390400005711643803648)
                        512))))))
            32768)
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        9223512774343131136
                        128)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256))
                    1024)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      720575940379279360
                      1024)
                    2048)
                  4096))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        144678138029277184
                        512)
                      1024)
                    2048)
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        140737488355328
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256))
                  1024)
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        140737488355328
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256))
                  1024))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1552238159979466902132713074982912
                        128)
                      256)
                    512)
                  1024)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512)
                      (Code.joinWords 512
                        10633823966279326983230456482242756608
                        10675362341147605604258700452876517376)))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 128
                        9223372036854775808
                        9223372036854775808)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256))
                    (Nat.shiftLeft
                      288230376151711744
                      1024))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        17592186044416
                        128)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        37383395344384
                        128)
                      (Code.joinWords 128
                        288230376151711744
                        17592186044416)))
                  4096))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2207613190144
                        128)
                      512)
                    2048)
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        170141183460469231731687303715884105728
                        170141183460469231731687303715884105728)
                      256)
                    512)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        17592186044416
                        128)
                      256)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        17592186044416
                        128)
                      256)
                    1024)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        81129638414606681695789005144064
                        256)
                      512)
                    1024)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2668840585286901401064675113219129344
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        512))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        512)
                      1024)))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        5316911983139663491615228241121378304
                        5316911983139663491615228241121378304)
                      1024)
                    2048)
                  4096))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        39614685720041976111359328256
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128))
                      512)
                    1024)
                  2048)
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          604462909807314587353088
                          170141183460469231731687303715884105728)
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          604462909807314587353088
                          170141183460469231731687303715884105728)
                        256)
                      512)
                    1024)))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1476179123965773138042910882660352
                        128)
                      256)
                    512)
                  1024)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    193428131138340667952988160
                    1024)
                  2048)
                4096)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        41103477866897391940009984
                        128)
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)
                      (Code.joinWords 128
                        664613997892457936451903530140172288
                        706152372760736557480147500773933056)))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          39614685720041976111359328256
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128))
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      170141183460469231731687303715884105728
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256))
                    (Nat.shiftLeft
                      5316911983139663491615228241121378304
                      1024)))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          604462909807314587353088
                          170141183460469231731687303715884105728)
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          604462909807314587353088
                          170141183460469231731687303715884105728)
                        256)
                      512)
                    1024)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319850366940556260600674336187298611200
                            333194773483368429265345327161346621440)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            2693757525484987478180494311424)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          149704303025276150185791270164073807872
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)
                        512))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256)
                      512)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            7605903601369376408980219232256
                            7764359926397905084167307132928)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            2693757525484987478180494311424)
                          256)
                        512)
                      1024))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256)
                      512)
                    2048))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      170141183460469231731687303715884105728
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128))
                    512)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      193428131138340667952988160
                      5316911983139663491615228241121378304)
                    1024))
                4096)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          5368919408946251973684407922264637440
                          2693757525484987478180494311424)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          23936488517845555367525588077704642560
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5368957438464258820566452823360798720
                          256)
                        (Nat.shiftLeft
                          121852913946938551218870595616768
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          41103477866897391940009984
                          128)
                        52004890505388025610376687736848384))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          52250814721832302114267048158691328
                          327212311183911714261336514887680)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          51926296168173875387483892138115072
                          2693757525484987478180494311424)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        51923760866973418928680898731704320
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        51923760866973418928680898731704320
                        256)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            5981525981032121428067131771261550592
                            706152372760736557480147500773933056)
                          51923760866973418928680898731704320)
                        5316911983139663491615228241121378304))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
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
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256)
                        512)
                      1024))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          128)
                        256)
                      512)
                    1024))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469836194597111030471458816
                          128)
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          128)
                        256)
                      512)
                    1024)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            43258576732788328326074996883456
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2693757525484987478180494311424
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40723275532331869523081590472704
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256)
                      512)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            7764359926397905084167307132928
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2693757525484987478180494311424
                            128)
                          256)
                        512)
                      1024))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256)
                      512)
                    2048))))
            (Code.joinWords 16384
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687444453372461056
                        128)
                      256)
                    512)
                  1024)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170143779608898499145501568964048715776
                        128)
                      256)
                    512)
                  1024))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          121852913946938551218870595616768
                          128)
                        256)
                      512)
                    1024)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40723275532331869523081590472704
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256)
                      512)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            367777130391215055109231017459712
                            327212311183911714261336514887680)
                          256)
                        (Nat.shiftLeft
                          365241829190758596306237611048960
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2693757525484987478180494311424
                          2693757525484987478180494311424)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256)
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256)))
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 128
                          14164585830083009770631193986112421888
                          872305872236268893232352641658388480)
                        13333818332717437350066877523390627840)
                      1024))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
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
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      170141183460469231731687303715884105728
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256))
                    (Nat.shiftLeft
                      5316911983139663491615228241121378304
                      1024)))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469836194597111030471458816
                          128)
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          128)
                        256)
                      512)
                    1024)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            327053854858883185586149426987008
                            2693757525484987478180494311424)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            2693757525484987478180494311424)
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
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256)
                      512)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            196608
                            128)
                          (Code.joinWords 128
                            7605903601369376408980219232256
                            2693757525502281300749597851660))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            196608
                            128)
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            2693757525502349119451431960576))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17592186044416
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            35184372088832
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            35321811042304
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17592186044416
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17592186044416
                            128)
                          256)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        170141183460469231731687303715884105728
                        170141183460469231731687303715884105728)
                      256)
                    512)
                  4096)
                (Code.joinWords 1024
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      136
                      128)
                    256)
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        136
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        17592186044416
                        128)
                      256))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2693757525484987478180494311424
                          2693757525484987478180494311424)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2668840585286901401064675113219129344
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256)
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256))
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          655360
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          327212311183911714261336514887680
                          2693757525484987478180494966784)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          45036546029518848
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2693757525484987478180494311424
                            2693757525485032532318709874688)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17592186044416
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17592186044416
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            47325901037371392
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            8589934592
                            128)
                          (Nat.shiftLeft
                            37520834297856
                            128)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            6189217855373514533208351624430354432
                            872305872236268893232352641658388480)
                          (Nat.shiftLeft
                            47306109828071424
                            128))
                        (Code.joinWords 256
                          5316911983139663491615228241121378304
                          (Nat.shiftLeft
                            17592186044416
                            128))))))))))))
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        512))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            140737488355328
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            140737488355328
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            9223372036854775808
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            9223372036854775808
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)))))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            312258420806120697111519296405685403648
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            312258420806120697111519296405685403648
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          218076468058462760398280845827244032
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51928673013049303317611698456625152
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          146215079536340746019418776630837903360
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5368916715188726488696929741770326016
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5368834951725011767900533204413579264
                          128)
                        256)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            14051230837395947520
                            128)
                          (Nat.shiftLeft
                            52004732049062997081701500648947712
                            128))
                        (Nat.shiftLeft
                          256208696187542534502424983651150397440
                          128)))))
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            32768
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884138496
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            32768
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884138496
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            140737488355328
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            140737488355328
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)))))
                8192)
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51923602410648390400005711643803648
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51923602410648390400005711643803648
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51923602410648390400005711643803648
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          128)
                        256)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            272159432136961524977054495592400551936
                            128)
                          (Nat.shiftLeft
                            51923602410648390400005711643803648
                            128))
                        (Nat.shiftLeft
                          272221739699263942908596861548351389696
                          128)))))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256)
                    512)
                  2048)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            298910145552132956919243612680542486528
                            312254348478567463924566988246638133248)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            298910145552132956919243612680542486528
                            312254348478567463924566988246638133248)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070602400912917605986812821504)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            316356262996809977751106080346722009088
                            316356262996809977751106080346722009088)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            317238953462760898447956264722689425408
                            317238953462760898447956264722689425408)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5649218982085892459841180006191464448
                        256)
                      (Nat.shiftLeft
                        5649305182326707979440481782009430016
                        256))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070602400912917605986812821504)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          498460498419343452338927647605129216
                          176538093190184139370036875193483264)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070602400912917605986812821504)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Nat.shiftLeft
                        5649305182326707979440481782009430016
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5649218982085892459841180006191464448
                        256)
                      (Nat.shiftLeft
                        5649305182326707979440481782009430016
                        256))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      170141183460469231731687303715884105728
                      128)
                    256)
                  512)
                4096)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256)
                      (Nat.shiftLeft
                        5649305182326707979440481782009430016
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          7975367974709495237422842361682067456
                          256)
                        (Nat.shiftLeft
                          2668840585286901401064675113219129344
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5649218982085892459841180006191464448
                        256)
                      (Nat.shiftLeft
                        5649305182326707979440481782009430016
                        256))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        5649305182326707979440481782009430016
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256)
                      (Nat.shiftLeft
                        5649305182326707979440481782009430016
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Nat.shiftLeft
                        5649305182326707979440481782009430016
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5649218982085892459841180006191464448
                        256)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          5649305182326707979440481782009430016)
                        5316911983139663491615228241121378304))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      170141183460469231731687303715884105728
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          9223512774343131136
                          128)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      332306998946228968225951765070086144
                      1024)))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        720575940379279360
                        332306998946228968225951765070086144)
                      1024)
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332312069548629881143557751882907648000
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            333194773483368429265345327161346621440
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          162165815485759736494264461354202038272
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40723275532331869523081590472704
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256)
                      512)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          329589156059339644389142833397760
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          21444186025748838105830949839678996480
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          329589156059339644389142833397760
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          384276395234810603413086545117184000
                          256)
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          384238365716803756531041644021022720
                          7764359926397905084167307132928)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          51928831469374331846286885544525824
                          256)
                        144678138029277184))))))
            (Code.joinWords 16384
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        140737488355328
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256))
                  1024)
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        140737488355328
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256))
                  1024))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          121694457621910022543683507716096
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          121852913946938551218870595616768
                          128)
                        256))
                    1024)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40723275532331869523081590472704
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256)
                      512)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          52288844239839148996311949254852608
                          256)
                        (Nat.shiftLeft
                          365241829190758596306237611048960
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        51923760866973418928680898731704320
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          51964325686180722269528793234276352
                          256)
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        51923760866973418928680898731704320
                        256)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            10966130965225555951456408247312842752
                            332306998946228968225951765070086144)
                          51923760866973418928680898731704320)
                        10675362341147605604258700452876517376)))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      170141183460469231731687303715884105728
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 128
                        9223372036854775808
                        9223372036854775808)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256))
                    (Nat.shiftLeft
                      332306998946228968514182141221797888
                      1024)))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          274877906944
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          17592186044416
                          128)
                        (Nat.shiftLeft
                          274877906944
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          37383395344384
                          128)
                        (Nat.shiftLeft
                          18014398509481984
                          128))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          288230376151711744
                          332306998946228968225969357256130560)
                        (Nat.shiftLeft
                          18014398509481984
                          128))))))
              (Code.joinWords 8192
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
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          21433801432031768450573888847020556288
                          21444186025748838105830949839678996480)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          329589156059339644389142833397760
                          329589156059339644389142833397760)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256)
                        (Nat.shiftLeft
                          2668840585286901401064675113219129344
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          48329179133701245932061809704960
                          7764359926397905084167307132928)
                        256)
                      (Nat.shiftLeft
                        40723275532331869523081590472704
                        256))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          329589156059339644389142833397760
                          329589156059339644389142833397760)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            14051230837395947520
                            128)
                          (Code.joinWords 128
                            21433801432031768450573888847020556288
                            176538093190184139370036875193483264))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            216172782113980416
                            128)
                          (Nat.shiftLeft
                            13889101250810609664
                            128)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          329589156059339644389142833397760
                          329589156059339644389142833397760)
                        256)))
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          7764359926397905084167307132928
                          2693757525484987478180494311424)
                        256)
                      (Nat.shiftLeft
                        2207613190144
                        128))
                    2048))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        170141183460469231731687303715884105728
                        170141183460469231731687303715884105728)
                      256)
                    512)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        64
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        17592186044480
                        128)
                      256))
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        274877906944
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        17867063951360
                        128)
                      256))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        405648192073033408478945025720320
                        256)
                      (Nat.shiftLeft
                        405648192073033408478945025720320
                        256))
                    1024)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256)
                        (Nat.shiftLeft
                          2668840585286901401064675113219129344
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256)
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256))
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18014398509481984
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18014398509481984
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18014398509481984
                          128)
                        256)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            5649218982085892459841180006191464448
                            332306998946228968225951765070086144)
                          (Nat.shiftLeft
                            18014398509481984
                            128))
                        5316911983139663491615228241121378304))
                    2048)))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      39614081257132168796771975168
                      (Code.joinWords 256
                        39614081257132168796771975168
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)))
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      77371252455336267181195264
                      1024)
                    2048))
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256))
                  2048))
              (Nat.shiftLeft
                (Code.joinWords 4096
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
                          176538093190184139370036875193483264
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          128)
                        256)))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        128)
                      1024)
                    2048))
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        75557863725914323419136
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        151706023262187352489984
                        512)
                      (Code.joinWords 512
                        77371252455336267181195264
                        75557863725914323419136))
                    2048))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        75557863725914323419136
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        75557863725914323419136
                        256)
                      512)
                    1024)))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        627189298506124754944
                        128)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        332306998946228968225951765070086144
                        332306998946228968225951765070086144)
                      1024)
                    2048)
                  4096))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      39614081257132168796771975168
                      (Code.joinWords 256
                        39614081257132168796771975168
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      170141183460469231731687303715884105728
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256))
                    (Nat.shiftLeft
                      5316911983217034744070564508302573568
                      1024)))
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256))
                  2048))
              (Code.joinWords 8192
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
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166153499473114484112975882535043072
                          176538093190184139370036875193483264)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          329589156059339644389142833397760
                          329589156059339644389142833397760)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          23926103924128485712268527085046202368
                          256)
                        (Nat.shiftLeft
                          23936488517845555367525588077704642560
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          124388215147395010021864002027520
                          2693757525484987478180494311424)
                        256)
                      (Nat.shiftLeft
                        121852913946938551218870595616768
                        256))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          329589156059339644389142833397760
                          329589156059339644389142833397760)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166153499473114484112975882535043072
                          176538093190184139370036875193483264)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          329589156059339644389142833397760
                          329589156059339644389142833397760)
                        256)))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2693757525484987478180494311424
                          2693757525484987478180494311424)
                        256)
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        128))
                    2048))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18889465931478580854784
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          75557863725914323419136
                          18889465931478580854784)
                        512))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        170141183460469231731687303715884105728
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128))
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          151706023262187352489984
                          1237940039285380274899124224)
                        512)
                      (Code.joinWords 512
                        77371252455336267181195264
                        (Code.joinWords 256
                          5316911983139739049478954155444797440
                          1237940039285380274899124224)))))
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1024
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        75557863725914323420160
                        256)
                      512))
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        18889465931478580854784
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        94447329657392904273920
                        256)
                      512))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        405648192073033408478945025720320
                        256)
                      (Nat.shiftLeft
                        405648192073033408478945025720320
                        256))
                    1024)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          23926103924128485712268527085046202368
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            59479150325039755395543859200
                            58028439341502200386093056)
                          (Code.joinWords 128
                            2668840585286901401064675113219129344
                            63134942003554394019855335424)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        121852913946938551218870595616768
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          627189298506124754944
                          128)
                        40723275532331869523081590472704))))
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1237940039285380274899124224
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1237940039285380274899124224
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1237940039285380274899124224
                          256)
                        512)
                      (Code.joinWords 512
                        (Code.joinWords 128
                          5649218982085892459841180006191464448
                          332306998946228968225951765070086144)
                        (Code.joinWords 256
                          5316911983139663491615228241121378304
                          1237940039285380274899124224))))
                  4096)))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
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
                    (Code.joinWords 512
                      170141183460469231731687303715884105728
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      332306998946228968225951765070086144
                      1024)))
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256))
                  2048))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            365083372865730067631050523148288
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40723275532331869523081590472704
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
                            40564819207303340847894502572032
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40723275532331869523081590472704
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256)
                      512)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          329589156059339644389142833397760
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          176538093190184139370036875193483264
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          329589156059339644389142833397760
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256)
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2693757525484987478180494311424
                          2693757525484987478180494311424)
                        256)
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        128))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687444453372461056
                          128)
                        256)
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170143779608898499145501568964048715776
                          128)
                        256)
                      512)
                    1024))
                (Code.joinWords 1024
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      2056
                      256)
                    512)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        2056
                        75557863725914323419136)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            121694457621910022543683507716096
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            196608
                            128)
                          (Nat.shiftLeft
                            40797551934688992339575538761740
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            75557863725914323419136
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            196608
                            128)
                          (Nat.shiftLeft
                            40802195399872666198757003493376
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            151115727451828646838272
                            160560460417567937265664)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            75557863725914323419136
                            75557863725914323419136)
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          655360
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          365241829190758596306237611048960
                          256)
                        (Nat.shiftLeft
                          40723275532331869523081591128064
                          256)))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            75557863725914323419136
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          3094887877145313644409520128
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            40726370495766878562640323411968
                            75557863725914323419136)
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            36893488147419103232
                            128)
                          (Code.joinWords 128
                            3104720582032411194126630912
                            161150756227926642917376))
                        512)
                      (Code.joinWords 512
                        (Code.joinWords 128
                          13666125331663666318292266338507292672
                          332306998946228968225951765070086144)
                        (Code.joinWords 256
                          13333818332717437350066877523390627840
                          (Code.joinWords 128
                            3104644433872874921097560064
                            75557863725914323419136)))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      170141183460469231731687303715884105728
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      170141183460469231731687303715884105728
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170141183460469231731687303715884105728
                          128)
                        256))
                    (Nat.shiftLeft
                      5649218982085892459841180006191464448
                      1024)))
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        128)
                      256))
                  2048))
              (Code.joinWords 8192
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
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166153499473114484112975882535043072
                          176538093190184139370036875193483264)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          329589156059339644389142833397760
                          329589156059339644389142833397760)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256)
                        (Nat.shiftLeft
                          2668840585286901401064675113219129344
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          43258576732788328326074996883456
                          2693757525484987478180494311424)
                        256)
                      (Nat.shiftLeft
                        40723275532331869523081590472704
                        256))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          329589156059339644389142833397760
                          329589156059339644389142833397760)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            176538093190184156717902639824633856)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            196608
                            128)
                          (Nat.shiftLeft
                            17361376563513262080
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            329589156059339644389142833397760
                            329589156059339662403541342879744)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17592186044416
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17592186044416
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2693757525484987478180494311424
                            2693757525485005528038253789184)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            35321811042304
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            332306998946228968225951765070086144
                            128)
                          (Nat.shiftLeft
                            18032265573433344
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            17592186044416
                            128)
                          256)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        170141183460469231731687303715884105728
                        170141183460469231731687303715884105728)
                      256)
                    512)
                  4096)
                (Code.joinWords 1024
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        64
                        128)
                      256)
                    (Nat.shiftLeft
                      1024
                      256))
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        64
                        128)
                      256)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        1024
                        75557863743506509463552)
                      256))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            75557863725914323419136
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            196608
                            128)
                          (Code.joinWords 128
                            2668840663277123876043632431863955456
                            78918677504442992524819169280)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            405649430013072693859219924844544
                            75557863725914323419136)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            40724513642376348286663717289984
                            160560460417567937265664)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          5316911983139663491615228241121378304
                          (Code.joinWords 128
                            1238034486615037667803398144
                            75557863725914323419136))
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18014673387388928
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18032265573433344
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            75557863743506509463552
                            128)
                          256)))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1237958928751311753479979008
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1238034486615037667803398144
                            75557863743506509463552)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            18052194221686784
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            36893488156009037824
                            128)
                          (Code.joinWords 128
                            1238120079507539680122896384
                            161150756265447477215232)))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            5649218982085892459841180006191464448
                            332306998946228968225951765070086144)
                          (Nat.shiftLeft
                            18032265573433344
                            128))
                        (Code.joinWords 256
                          5316911983139663491615228241121378304
                          (Code.joinWords 128
                            1238034486615037667803398144
                            75557863743506509463552)))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (448 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage007
