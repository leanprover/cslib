/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 641–704 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage010

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            317592029649141266726696338473076391936
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807089952750676576567296
                            317596183482899710473741459600741236736)
                          256)
                        512))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            297747071055821155530452781502797185024
                            297747071055821155530452781502797185024)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            297750965278465056651174179375044100096
                            10643828264816328169667068463939584)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            297747071105338757101867992498762153984
                            10384593717069655257060992658440192)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            297750965327982658222589390371009069056
                            10384593717069655257060992658440192)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            297747071055821155541981996548865654784
                            10384593717069655257060992658440192)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            297750965278465056662703535158600925184
                            10384593717069655257060992658440192)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            297747071105338757113397207546978107392
                            20769187434139310514121985316880384)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            297750965327982658234118746156713377792
                            20769504346789367571472359492681728)
                          256)
                        512)))))
              16384)
            32768)
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        255880293552445008480539468949838888960
                        128)
                      256)
                    512)
                  1024)
                4096)
              16384)
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          14288957565772601813812125775167488
                          128)
                        256)
                      512)
                    1024)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          162259276829213363391578010288128
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)
                        (Nat.shiftLeft
                          2658455991569831745951729308636545024
                          256))
                      1024))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          13292279957849158729038070602803445760
                          256)
                        (Nat.shiftLeft
                          2658455991569831745951729308636545024
                          256)))
                    2048)))
              16384))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 128
                      255876389188596305533982859103966330880
                      255876389188596305533982859103966330880)
                    256)
                  512)
                4096)
              16384)
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          255876389188596305543242259937840070656
                          10384593717069655257060992658440192)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      1024))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256))
                    2048)))
              16384))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          265849655638903904914846201506326118400
                          128)
                        256)
                      512)
                    1024)
                  2048)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          14441075638442231183520714664706048
                          128)
                        256)
                      512)
                    1024)
                  2048))
              16384)
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        10141204801825835211973625643008
                        128)
                      256)
                    1024)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          830767497365572420564879412675215360
                          166153499511800110340644016125640704)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          830767497365572420564879412675215360
                          166153499473114484112975882535043072)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          830767497365572420564879412675215360
                          166153499511800110340644016125640704)
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
                            64969912516631664408894967943448756224
                            14441075637799989341850442915643392)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            3894222643901120721397872246915072
                            14441075638442231183520714664706048)
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)))))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
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
                        256)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        664613997892457936451903530140172288
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          664624139097259762287115503765815296
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)
                          256)))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          339835829391104468287320984747455283200
                          128)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166812677785233163401754168201838592
                            166153499473114484112975882535043072)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            2535301200456458802993406410752)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166488159231574736674971012181262336
                          166153499473114484112975882535043072)
                        256))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10141204801825835211973625643008
                            10141204801825835211973625643008)
                          256)
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5317317631331736525023707186147098624
                            324518553658426726783156020576256)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            166478018065458537067427172146216960)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            5316993112778078098296924030126522368
                            324518553658426726783156020576256))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            166194064292321787453823777037615104)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Code.joinWords 128
                            5316995648079278554755727023532933120
                            43100120407759799650887908982784)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            166153499511800110340644016125640704)
                          256)
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2758407706096627177656826174898176
                            128)
                          (Nat.shiftLeft
                            14441075637799989341850442915643392
                            128))
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          2606289634069239649477221790253056
                          128)
                        (Nat.shiftLeft
                          14288957565772601813670838530998272
                          128))
                      512)
                    1024))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            333605073160862675133084389152391168000
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2758407706701090087464140762251264
                            128)
                          (Nat.shiftLeft
                            87133231657929817982947663273787392
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)))))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256)
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166153499473114484112975882535043072
                          166153499473114484112975882535043072)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2824609491042946229920590003095732224
                            166153499511800110340644016125640704)
                          256)
                        (Nat.shiftLeft
                          2658455991569831745951729308636545024
                          256))
                      1024)))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            339835829391104468287320984747455283200
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2606289634069239649617959278608384
                            128)
                          (Nat.shiftLeft
                            1333132359633618819460558193397071872
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            651572408517309912369305447563264
                            2535301200456458802993406410752)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            172400481631039198603551635931136
                            41539008693578735142944718985363456)
                          256)
                        (Nat.shiftLeft
                          41539008693578735142944718985363456
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          41549149898380560978156692611006464
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2658455991569831745807614120560689152
                            41539008693578735142944718985363456)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2700319518817068907821457183642484736
                            324518553658426726783156020576256)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          41701267970407948506336296995651584
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            208017026759037272210371891131580416)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            41539008693578735142944718985363456
                            324518553658426726783156020576256)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2824609491042946229920590003095732224
                            207733072985900522596768496022978560)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2699997535564610937409361832952463360
                            43100120407759799650887908982784)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2824609491042946229920590003095732224
                            207692508205378845483588735111004160)
                          256)
                        (Nat.shiftLeft
                          2699995000263410481094674027621908480
                          256))))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2758407706096627177656826174898176)
                          (Code.joinWords 128
                            3894222643901120721397872246915072
                            14441075637799989341850442915643392))
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      170805797458361689668139207246024278016
                      (Code.joinWords 128
                        255876389188596305533982859103966330880
                        10384593717069655257060992658440192))
                    512))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            319017315136809076910727959715447308288
                            332309757413356186738827675091419004928)
                          (Code.joinWords 128
                            320263466442510671184639540831161679872
                            333607831628222007403326307975267614720))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2758407706701090087464140762251264)
                          (Code.joinWords 128
                            86970972380458362777885813514436608
                            87133231657929817982947663273787392))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)))))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          41539008693578735142944718985363456
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5483065482612777975728204123656421376
                            218077101883762874512981594178846720)
                          256)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256)))
                    2048))
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            218401620437421301239764750199422976)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            41579573522457445040709646885584896
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166153499473114484112975882535043072
                          218077101932119907297566761167093760)
                        256)))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          41549149908051967535073726008655872
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316911983139663491615228241121378304
                            41539008703250141699861752383012864)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5317236501693321918630241773293666304
                            324518553658426726783156020576256)
                          256)))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        170805797458361689677362579282879053824
                        (Code.joinWords 128
                          255876389188596305543242259937840070656
                          1329227995784915872903807060280344576))
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5483065482612777975728204123656421376
                            207692508176364625812837634918055936)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316914518440863948074031234527789056
                            2535301200456458802993406410752)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5483065482612777975728204123656421376
                            218077101893434281069898627576496128)
                          256)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          91270843216432516907762630787072
                          41539008693578735142944718985363456)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          41549149908051967535073726008655872
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            41539008703250141699861752383012864
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            218401620476106927467432883790020608)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            207733072995571929153685529420627968)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            43100120407759799650887908982784)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166153499473114484112975882535043072
                          218077101932119907297566761167093760)
                        256))))))))))
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Code.joinWords 32768
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          317592029649141266726696338473076391936
                          128)
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          212679075523534013112748413203572064256
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          317596183492841916411802211736235278336
                          128)
                        256)))
                  2048)
                4096)
              8192)
            16384)
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 4096
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297747071055821155530452781502797185024
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297747071055821155530452781502797185024
                          128)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297750965278465056651174179375044100096
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10643828264816328169667068463939584
                          128)
                        256)))
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297747071105338757101867992498762153984
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297750965327983262685499197685596422144
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256))))
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297747071055821155541981996548865654784
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297750965278465056662703394421112569856
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)))
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297747071105338757113397207546978107392
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          128)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          297750965327983262697028412733812375552
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          128)
                        256)))))
              8192)
            16384))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            82416029961308685240757435609628278784
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            14288957565772601813670838530998272
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)
                        256)))
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          333605073160862675133084389152391168000
                          128)
                        256)
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        10633823966279326983230456482242756608
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10633986225556156196593848060253044736
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2659267287953977812624572010612129792
                            40564819207303340847894502572032)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2658455991569831745807614120560689152
                            40564819207303340847894502572032)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658942769400319385897788854591553536
                          256)
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256))))))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2535301200456458802993406410752
                          2535301200456458802993406410752)
                        256)
                      512)
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256))
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            3894222643901120721397872246915072
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            14288957565772601813812125775167488
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            651572408517309912369305447563264
                            2535301200456458802993406410752))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            162259276829213363391578010288128
                            332312069548629881143557751882907648)
                          256)
                        (Nat.shiftLeft
                          162259276829213363391578010288128
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2658455991569831745807614120560689152
                            332312069548629881143557751882907648)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            2658780510123490172678512464657121280
                            324518553658426726783156020576256)))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332636588102288307870340907903483904
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2658455991569831745807614120560689152
                            332352634367837184484405646385479680)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            2658458526871032202266417113967099904
                            43100120407759799650887908982784)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2658455991569831745807614120560689152
                            332312069548629881143557751882907648)
                          256)
                        (Nat.shiftLeft
                          2658455991569831745951729308636545024
                          256))))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          255211775190703847597530955573826158592
                          82412135738664784120036037737381363712)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          255876389188596305533982859103966330880
                          10384593717069655257060992658440192)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5317561020246980345068794553162530816
                            649037107316853453566312041152512)
                          256)
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5317236501693321918342011397141954560
                            332631517577258647408071188271857664)
                          256)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256))))
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          170141183500083312988819472512656080896
                          180775007468838520050620689544697085952)
                        256)
                      (Code.joinWords 256
                        (Code.joinWords 128
                          319014718988379809496913694467282698240
                          319014719047800931382611947662440660992)
                        (Code.joinWords 128
                          320260870294081403770825275582997069824
                          333605073223001462261276328732288614400)))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        5316911983139663491615228241121378304
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316993112778078098296924030126522368
                            332631517577258647408071188271857664)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            730166745731460135262101046296576
                            40564819207303340847894502572032)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          405648192073033408478945025720320
                          332306999023600220681288032251281408)
                        256)))))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          128)
                        256))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332352634445208436939741913566674944
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            43258576732788328326074996883456)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069626001133598894019064102912
                          128)
                        256))
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069626001133598894019064102912
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316911983139663491615228241121378304
                            332312069626001133598894019064102912)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            5317236501693321918630241773293666304
                            324518553658426726783156020576256))))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        255211775190703847606754327610680934400
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          255876389188596305543242259937840070656
                          10384593717069655257060992658440192)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316911983139663491615228241121378304
                            332312069626001133598894019064102912)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            5316914518440863948074031234527789056
                            2535301200456458802993406410752)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316911983139663491615228241121378304
                            332312069626001133598894019064102912)
                          256)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            81129638414606681695789005144064
                            332312069626001133598894019064102912)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            81129638414606681695789005144064
                            324518553658426726783156020576256)))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069626001133598894019064102912
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332312069626001133598894019064102912
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332636588179659560325677175084679168
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            332352634445208436939741913566674944
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            43258576732788328326074996883456)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069626001133598894019064102912
                          128)
                        256)))))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        265845599156983174580761412056068915200
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        265845599156983174580761412056068915200
                        128)
                      256))
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          265845599199073135916464341402639138816
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306999023600220681288032251281408)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306998946228968225951765070086144)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306999023600220681288032251281408)
                        256)))))
              16384)
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        5070602400912917605986812821504
                        128)
                      256)
                    1024)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256)
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256))))
                8192)
              16384))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        512))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          255211775190703847597530955573826158592
                          265845599156983174580761412056068915200)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          64966018293987763288173570071201841152
                          10384593717069655257060992658440192)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332956036053545821679518077111238656
                            332306998946228968225951765070086144)
                          256)
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332631517499887394952734921090662400
                            332306999023600220681288032251281408)
                          256)
                        (Nat.shiftLeft
                          5317236501693321918630241773293666304
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          255211775230317928854663124370598133760
                          265845599199073135916464341402639138816)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332631517577258647408071188271857664)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            5316993112778078098585154406278234112
                            324518553658426726783156020576256))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332347563765436271566799659572658176)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Code.joinWords 128
                            5316993112778078098585154406278234112
                            40564819207303340847894502572032)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332306999023600220681288032251281408)
                          256)
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256)))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316995648079278555043957399684644864
                            43258576732788328326074996883456)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256)
                        512)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        332306998946228968225951765070086144
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          332312069548629881143557751882907648
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            5317236501693321918630241773293666304
                            324518553658426726783156020576256))))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          128)
                        (Code.joinWords 128
                          170141183460469231740910675752738881536
                          338953138925153547605170549555225165824))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          319014718988379809510748752522564861952
                          128)
                        (Code.joinWords 128
                          170805797458361689677398608079898017792
                          339835829391104468302059014528025231360)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          654107709717766371172298853974016
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2535301200456458802993406410752
                            2535301200456458802993406410752)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          329589156059339644389142833397760
                          256)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5070602400912917605986812821504
                            5070602400912917605986812821504)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            5316993112778078098585154406278234112
                            324518553658426726783156020576256)))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            5317317631331736525311937562298810368
                            324518553658426726783156020576256))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            5316993112778078098585154406278234112
                            324518553658426726783156020576256))))
                    (Code.joinWords 1024
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
                          (Code.joinWords 128
                            5316995648079278555043957399684644864
                            43258576732788328326074996883456)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
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
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306998946228968225951765070086144)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          41539008693578735142944718985363456
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2990762990516060714033565885630775296
                            332306999023600220681288032251281408)
                          256)
                        (Nat.shiftLeft
                          2710379593980480136207619832204492800
                          256))))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          180775007426748558714917760198126862336
                          128)
                        (Nat.shiftLeft
                          265845599156983174580761412056068915200
                          128))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        (Nat.shiftLeft
                          3894222643901120721397872246915072
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          2606289634069239649477221790253056
                          128)
                        (Nat.shiftLeft
                          14288957565772601813670838530998272
                          128)))
                    1024))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          180775007466362639972049928994898837504
                          128)
                        (Nat.shiftLeft
                          265845599199073135916464341402639138816
                          128))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          83076749736557242056487941267521536
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          41701267970407948508588096809336832
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332631517577258647408071188271857664)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            41539008693578735145196518799048704
                            324518553658426726783156020576256)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2990762990516060714033565885630775296
                            332347563765436271566799659572658176)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2699995000263410480952810639359737856
                            40564819207303340847894502572032)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2990762990516060714033565885630775296
                            332306999023600220681288032251281408)
                          256)
                        (Nat.shiftLeft
                          2710379593980480136209871632018178048
                          256)))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            2710704112534138562934402988225069056
                            324518553658426726783156020576256)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            41541543994779191603999512205459456
                            2535301200456458802993406410752))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256)
                        (Nat.shiftLeft
                          2710379593980480136353986820094033920
                          256)))
                    2048))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319017315136809076910727959715447308288
                            128)
                          (Nat.shiftLeft
                            338955735073582815018984814803389775872
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319848092775379451170963109157030330368
                            128)
                          (Nat.shiftLeft
                            339838435680738537541670211152982835200
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2596148429267413814265248164610048
                            128)
                          (Nat.shiftLeft
                            1333122218428816993625204932527259648
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2606289634069239649617959278608384
                            128)
                          (Nat.shiftLeft
                            1333132359633618819460558193397071872
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            651572408517309912369305447563264
                            2535301200456458802993406410752))
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          167329879230126280997564823109632
                          256)
                        (Nat.shiftLeft
                          41539008693578735142944718985363456
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            2710704112534138563078518176300924928
                            324518553658426726783156020576256)))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          41701267970407948508588096809336832
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            41539008693578735145196518799048704
                            324518553658426726783156020576256)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2658455991569831745807614120560689152
                            40564819207303340847894502572032)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            2699997535564610937411613632766148608
                            43100120407759799650887908982784)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658455991569831745807614120560689152
                          256)
                        (Nat.shiftLeft
                          2710379593980480136353986820094033920
                          256))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306998946228968225951765070086144)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306999023600220681288032251281408)
                        256)
                      1024))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          180775007426748558714917760198126862336
                          128)
                        (Code.joinWords 128
                          255211775190703847597530955573826158592
                          265845599156983174580761412056068915200))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        255211775190703847597530955573826158592
                        256)
                      (Code.joinWords 256
                        170805797458361689668139207246024278016
                        (Code.joinWords 128
                          255876389188596305533982859103966330880
                          10384593717069655257060992658440192)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5649218982085892459841180006191464448
                            332306998946228968225951765070086144)
                          256)
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5649218982085892459841180006191464448
                            332306999023600220681288032251281408)
                          256)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256)))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          180775007466362639972049928994898837504
                          128)
                        (Code.joinWords 128
                          255211775230317928854663124370598133760
                          265845599199073135916464341402639138816))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749736557242056487941267521536)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332631517577258647408071188271857664)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            332347563765436271566799659572658176)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306999023600220681288032251281408)
                        256))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256))
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            324518553658426726783156020576256
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
                        (Code.joinWords 128
                          2535301200456458802993406410752
                          43258576732788328326074996883456))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            5317236501693321918630241773293666304
                            324518553658426726783156020576256))))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          255211775190703847606754327610680934400
                          1329227995784915872903807060280344576)
                        256)
                      (Code.joinWords 256
                        170805797458361689677362579282879053824
                        (Code.joinWords 128
                          255876389188596305543242259937840070656
                          1329227995784915872903807060280344576)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            5316914518440863948074031234527789056
                            2535301200456458802993406410752)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          86200240815519599301775817965568
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5070602400912917605986812821504
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256))
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128))))
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
                        (Code.joinWords 128
                          2535301200456458802993406410752
                          43258576732788328326074996883456))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (640 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage010
