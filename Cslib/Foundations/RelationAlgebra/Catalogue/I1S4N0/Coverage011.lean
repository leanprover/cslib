/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 705–768 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage011

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            317564770090633958881646553367347986432
                            128)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            317560875937585499344500127824586211328
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            317565029394778057374273704896753565696
                            128)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            317560875867990057778074862876127920128
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6521621829590660968910077531839791104
                            128)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6531909448307612541293847633824055296
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            6532006423578533542041476725689286656
                            128)
                          256)
                        512))))
                8192)
              16384)
            32768)
          65536)
        (Code.joinWords 65536
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          338496216801602482773898146475086446592
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
                          10633823966279326983806917234546180096
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10633986225556156197170308812556468224
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10633823966279326983806917234546180096
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10633986225556156197170308812556468224
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10633986225556156197170308812556468224
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10633986225556156197170308812556468224
                          256)
                        512)))))
              16384)
            32768)
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        338496216801602482773898146475086446592
                        128)
                      256)
                    512)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316993112778078098585154406278234112
                          256)
                        512)))))
              16384)
            32768)))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          333511611879547835363962779798362652672
                          128)
                        256)
                      512)
                    1024)
                  2048)
                8192)
              16384)
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          664613998047200441362576064502562816
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          664613998047200441362576064502562816
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          664624139252002267197788038128205824
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          664624139252002267197788038128205824
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          664624139252002267197788038128205824
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          664624139252002267197788038128205824
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
                            255211775190703847597530955573826158592
                            333511611817409048235770840218465206272)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128))
                        512))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            320177793544344846528768787641729548288
                            333511611879547835363962779798362652672)
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256))
                        512))
                    2048)))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512)
                          256)
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          664613998047200441362576064502562816
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          664624139252002267197788038128205824
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            664613997892457936451903530140172288
                            665273176359319120651354350169358336)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            664613997892457936451903530140172288
                            664948657805660693924571194148782080)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          324518553658426726783156020576256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664613997892457936451903530140172288
                          664613998047200441362576064502562816)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664613997892457936451903530140172288
                          664613998047200441362576064502562816)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664624139097259762287115503765815296
                          664624139252002267197788038128205824)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664624139097259762287115503765815296
                          664624139252002267197788038128205824)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          665273176204576615740681815806967808
                          665273176359319120651354350169358336)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            664948657650918189013898659786391552
                            664948657805660693924571194148782080)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
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
                            332306998946228968225951765070086144000
                            128)
                          (Nat.shiftLeft
                            333511611817409048235770840218465206272
                            128))
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319845486485745381917478573879957913600
                            128)
                          (Nat.shiftLeft
                            338496216801602482759160116694516498432
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128))
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            66461399789245793645190353014017228800
                            128)
                          (Nat.shiftLeft
                            22482645397697588795459974940464250880
                            128))
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256))
                        512))
                    2048)))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633986225556156196593848060253044736
                          256)
                        (Nat.shiftLeft
                          162259276829213363391578010288128
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664624139097259762287115503765815296
                          10141204801825835211973625643008)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            11299259401760732812334529876060012544
                            659178312118679288778285666795520)
                          256)
                        (Nat.shiftLeft
                          811296384146066816957890051440640
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            11298934883207074385607746720039436288
                            334659758460252561995129646219264)
                          256)
                        (Nat.shiftLeft
                          486777830487640090174734030864384
                          256)))))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            63969097297149076383495714775991582720
                            128)
                          (Nat.shiftLeft
                            39928762842132824464266459699971358720
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)))
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
                            128)))))
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            11298437964171784919682360012382928896
                            664624139252002267197788038128205824)
                          256)
                        (Nat.shiftLeft
                          10633986225556156197170308812556468224
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664613997892457936451903530140172288
                          664613998047200441362576064502562816)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          11298610364653415958880963564018860032
                          664624139252002267197788038128205824)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633823966279326983230456482242756608
                          256)
                        (Nat.shiftLeft
                          10633823966279326983806917234546180096
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          11298610364653415958880963564018860032
                          256)
                        (Nat.shiftLeft
                          10633986225556156197170308812556468224
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            11299259401760732812334529876060012544
                            659178312118679288778285666795520)
                          256)
                        (Nat.shiftLeft
                          811296384146066816957890051440640
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            11298934883207074385607746720039436288
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
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
                            319014718988379809496913694467282698240
                            162165815485759736494264461354202038272)
                          (Code.joinWords 128
                            22430722428870455355251744142230814720
                            22472260803738733976279988112864575488))
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          319845486485745381917478573879957913600
                          128)
                        (Nat.shiftLeft
                          338496216801602482759160116694516498432
                          128))
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256))
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            63802943797675961899382738893456539648
                            23926103924128485712268527085046202368)
                          (Code.joinWords 128
                            22430722429102569112617752943774400512
                            22482645397697588795459974940464250880))
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256))
                        512))
                    2048)))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664624139097259762287115503765815296
                          10141204801825835211973625643008)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664624139097259762287115503765815296
                          10141204801825835211973625643008)
                        256))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664624139097259762287115503765815296
                          10141204801825835211973625643008)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5982266288982654714037605845933490176
                            659178312118679288778285666795520)
                          256)
                        (Nat.shiftLeft
                          730166745731460135262101046296576
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5317327772536538350858919159772741632
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664613997892457936451903530140172288
                          664613998047200441362576064502562816)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664624139097259762287115503765815296
                          664624139252002267197788038128205824)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          63969097297149076383495714775991582720
                          128)
                        (Nat.shiftLeft
                          71954849865575641277042561058600910848
                          128))
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            659178312118679288778285666795520
                            659178312118679288778285666795520)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          324518553658426726783156020576256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5981525981032121428067131771261550592
                            664624139252002267197788038128205824)
                          256)
                        (Nat.shiftLeft
                          81129638414606969926165156855808
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664613997892457936451903530140172288
                          664613998047200441362576064502562816)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5981617251875337860584039533892337664
                            664624139252002267197788038128205824)
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606969926165156855808
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5317652291090196777585702315793317888
                            659178312118679288778285666795520)
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5317317631331736525023707186147098624
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)))))))))))
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Nat.shiftLeft
            (Nat.shiftLeft
              (Code.joinWords 4096
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          317564770090633958881646553367347986432
                          128)
                        256)
                      512)
                    1024)
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          317560875937585499344500127824586211328
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18983286438128545219567265338636632064
                          128)
                        256)
                      512)))
                (Code.joinWords 2048
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          317560875867990057778074862876127920128
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          317565029325181705571709091124552400896
                          128)
                        256)
                      512))
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18993421908791198849767038823952285696
                          128)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          18993671001979404733708635738143195136
                          128)
                        256)
                      512))))
              8192)
            16384)
          32768)
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
                            255211775190703847597530955573826158592
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338496216801602482759160116694516498432
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128))
                        512)))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10633823966279326983806917234546180096
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10633986225556156197170308812556468224
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10633823966279326983230456482242756608
                            649037107316853453566312041152512)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            10634635262663473050623875124597620736
                            649037107316853453566312041152512)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10633823966279326983230456482242756608
                            324518553658426726783156020576256)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          10634310744109814623897091968577044480))))
                  4096))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512)
                          256)
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            337623910929368631732266742494944821248
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            338496216801602482773898146475086446592
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)))
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
                            128)))))
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633823966279326983230456482242756608
                          256)
                        (Nat.shiftLeft
                          10633823966279326983806917234546180096
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633986225556156196593848060253044736
                          256)
                        (Nat.shiftLeft
                          10633986225556156197170308812556468224
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633823966279326983230456482242756608
                          256)
                        (Nat.shiftLeft
                          10633823966279326983806917234546180096
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633986225556156196593848060253044736
                          256)
                        (Nat.shiftLeft
                          10633986225556156197170308812556468224
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10634635262663473050047414372294197248
                          256)
                        (Nat.shiftLeft
                          10634635262663473050623875124597620736
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10634310744109814623320631216273620992
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          10634310744109814623897091968577044480
                          256))))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          255211775190703847597530955573826158592
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          338496216801602482759160116694516498432
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          324518553658426726783156020576256)
                        512)))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          81129638414606969926165156855808
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316911983139663491615228241121378304
                            649037107316853453566312041152512)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            730166745731460423492477198008320
                            649037107316853453566312041152512)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5316911983139663491615228241121378304
                            324518553658426726783156020576256)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          405648192073033696709321177432064))))
                  4096))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512)
                          256)
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          71778311772385457151505330438875906048
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          71944465271858571626433214881388822528
                          128)
                        256))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          324518553658426726783156020576256))))
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          288230376151711744
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606969926165156855808
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606969926165156855808
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606969926165156855808
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5317317631331736525023707186147098624
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256))))))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        333511611879547835363962779798362652672
                        128)
                      256)
                    512)
                  2048)
                8192)
              16384)
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306999023600220681288032251281408
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306999023600220681288032251281408
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069626001133598894019064102912
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069626001133598894019064102912
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069626001133598894019064102912
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332312069626001133598894019064102912
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
                        (Code.joinWords 128
                          255211775190703847597530955573826158592
                          333511611817409048235770840218465206272)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          128)))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          64301404355748540994785928537763217408
                          66959860310189842968589051444747829248)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          324518553658426726783156020576256)))
                    2048)))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512)
                          256)
                        (Nat.shiftLeft
                          649037107316853453566312041152512
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          332306999023600220681288032251281408
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          5070679772165372942253994016768
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            654107787089018826508566035169280)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332306998946228968225951765070086144
                            329589233430592099725410014593024)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          324518553658426726783156020576256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          77371252455336267181195264)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306999023600220681288032251281408)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070679772165372942253994016768)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070679772165372942253994016768)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070679772165372942253994016768)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332636588102288307870340907903483904
                            329589156059339644389142833397760)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633986225556156196593848060253044736
                          256)
                        (Nat.shiftLeft
                          162259276829213363391578010288128
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633986225556156196593848060253044736
                          256)
                        (Nat.shiftLeft
                          162259276829213363391578010288128
                          256)))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          332306998946228968225951765070086144000
                          128)
                        (Nat.shiftLeft
                          333511611817409048235770840218465206272
                          128))
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            319014718988379809496913694467282698240
                            128)
                          (Nat.shiftLeft
                            39876839873547476187114211808410337280
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            149704303025276150185791270164073807872
                            128)
                          (Nat.shiftLeft
                            39918378248415754808142455779044098048
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)))
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
                            128))))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          66461399789245793645190353014017228800
                          128)
                        (Nat.shiftLeft
                          66970244881623991916709267489222033408
                          128))
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633823966279326983230456482242756608
                          256)
                        (Nat.shiftLeft
                          10633823966279326983806917234546180096
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633986225556156196593848060253044736
                          256)
                        (Nat.shiftLeft
                          10633986225556156197170308812556468224
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            811296384146066816957890051440640
                            649037107316853453566312041152512)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            811296384146066816957890051440640
                            649037107316853453566312041152512)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          324518553658426726783156020576256)))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633986225556156196593848060253044736
                          256)
                        (Nat.shiftLeft
                          162259276829213363391578010288128
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070602400912917605986812821504)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10966947332212102931190972124177104896
                            654107709717766371172298853974016)
                          256)
                        (Nat.shiftLeft
                          811296384146066816957890051440640
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332798847379117521233732485913772032
                            329589156059339644389142833397760)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)))))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            63802943797675961899382738893456539648
                            128)
                          (Nat.shiftLeft
                            39876839873547476187978902936865472512
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21433801432031768450573888847020556288
                            128)
                          (Nat.shiftLeft
                            39928762842132824464266459699971358720
                            128)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)))
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
                            128)))))
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10966130965225555951456408247312842752
                            5070679772165372942253994016768)
                          256)
                        (Nat.shiftLeft
                          10633986225556156197170308812556468224
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306999023600220681288032251281408)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070679772165372942253994016768)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633823966279326983230456482242756608
                          256)
                        (Nat.shiftLeft
                          10633823966279326983806917234546180096
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10966298295104786077737405812135952384
                            5070602400912917605986812821504)
                          256)
                        (Nat.shiftLeft
                          10633986225556156197170308812556468224
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            333123365932775947960515641934348288
                            5070602400912917605986812821504)
                          256)
                        (Nat.shiftLeft
                          811296384146066816957890051440640
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332636588102288307870340907903483904
                            329589156059339644389142833397760)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)))
                    2048)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          319014718988379809496913694467282698240
                          332306998946228968225951765070086144000)
                        (Code.joinWords 128
                          320177793484691610885704525645027999744
                          333511611817409048235770840218465206272))
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          128)
                        (Nat.shiftLeft
                          337623910929368631717566993311207522304
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          319845486485745381917478573879957913600
                          128)
                        (Nat.shiftLeft
                          338496216801602482759160116694516498432
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            324518553658426726783156020576256
                            324518553658426726783156020576256)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            324518553658426726783156020576256
                            128)
                          324518553658426726783156020576256)))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          63802943797675961899382738893456539648
                          66461399789245793645190353014017228800)
                        (Code.joinWords 128
                          64301404296327419109087675342605254656
                          66970244881469249411798594954859642880))
                      512)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606969926165156855808
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5317642149885394951750490342167674880
                            649037107316853453566312041152512)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            730166745731460135262101046296576
                            649037107316853453566312041152512)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5317317631331736525023707186147098624
                            324518553658426726783156020576256)
                          256)
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070602400912917605986812821504)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070602400912917605986812821504)
                        256))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316993112778078098296924030126522368
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070602400912917605986812821504)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5649954219434024832894048094050582528
                            5070602400912917605986812821504)
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5649629700880366406167264938030006272
                            329589156059339644389142833397760)
                          256)
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306999023600220681288032251281408)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332312069548629881143557751882907648
                          5070679772165372942253994016768)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          63802943797675961899382738893456539648
                          128)
                        (Nat.shiftLeft
                          71778311772385457137670272383593742336
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          63969097297149076383495714775991582720
                          128)
                        (Nat.shiftLeft
                          71954849865575641276466100306297487360
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332961106655946734597124063924060160
                            654107709717766371172298853974016)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            649037107316853453566312041152512)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            332636588102288307870340907903483904
                            329589156059339644389142833397760)
                          256)
                        (Nat.shiftLeft
                          324518553658426726783156020576256
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5649218982085892459841180006191464448
                            5070679772165372942253994016768)
                          256)
                        (Nat.shiftLeft
                          81129638414606969926165156855808
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          332306998946228968225951765070086144
                          332306999023600220681288032251281408)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5649305182326707979440481782009430016
                            5070602400912917605986812821504)
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          5316911983139663491615228241121378304
                          256)
                        (Nat.shiftLeft
                          5316911983139663491903458617273090048
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5649305182326707979440481782009430016
                            5070602400912917605986812821504)
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5649305182326707979440481782009430016
                            5070602400912917605986812821504)
                          256)
                        (Nat.shiftLeft
                          81129638414606681695789005144064
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            5649629700880366406167264938030006272
                            329589156059339644389142833397760)
                          256)
                        (Nat.shiftLeft
                          405648192073033408478945025720320
                          256))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (704 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage011
