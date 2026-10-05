/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 257–320 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage004

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
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
                            256212605621993638361683026701721796608)
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            255876389188596305533983070227378733056
                            255876389188596305533983070244558602240)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            255880293552445008480539468949838888960
                            255880293552445008480539468949838888960)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            256208696187542534516047246624039108608
                            256208696187542534516047246624039108608)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            255211775190703847597747128355939942400
                            128)
                          1000830431289790777990717989130862592)
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          256208696187542534502208810869036417024
                          256212590410186435622930208741283332096)
                        256)
                      512)
                    1024)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          17179869184
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1125899906842624
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1125899906842624
                          256)
                        512)))))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        140737488355328
                        256)
                      (Nat.shiftLeft
                        140737488355328
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        256)
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        256)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13907115649320091648
                            13979173243358019584)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            297747071055821155530452781502797185024
                            297747071055821155530452781502797185024)
                          256))
                      (Nat.shiftLeft
                        13835058055282163712
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          297747071055821155530452781502797185024
                          41538374868278621028243970633760768)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          316356262996809977751106080346722009088
                          41538374868278621028243970633760768)
                        256)))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            146879693534233203972083638819511861248
                            41538374868278621028243970633760768)
                          256)
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            146879693534233203972083638819511861248
                            41538374868278621028243970633760768)
                          256)
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        4611686018427387904
                        256)
                      (Nat.shiftLeft
                        4683743612465315840
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          85901359227600188286408531270617268224
                          41538374868278621028243970633760768)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          104510551168589010507061830114542092288
                          41538374868278621028243970633760768)
                        256)))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            104510551168589010511745573727007408128
                            51922968585348276285304963292200960)
                          256)
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            104510551168589010511745573727007408128
                            51922968585348276285304963292200960)
                          256)
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          256)))
                    2048)))))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        255381824180471463430594730825311322112
                        (Nat.shiftLeft
                          255880293552445008480539468949838888960
                          128))
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1298074214633706907132624082305024
                      512)
                    1024))
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          255464903465509221129110021759985254400
                          128)
                        (Nat.shiftLeft
                          256212605621993638361683026701721796608
                          128))
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1267650600228229401496703205376
                        128)
                      512)
                    1024)))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        158456325028528675187087900672
                        256)
                      (Nat.shiftLeft
                        633825300114114700748351602688
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        2710378960155180022092919083852890112
                        256)
                      (Nat.shiftLeft
                        51922968585348276285304963292200960
                        256))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          3327582825599102178928845914112
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          792281625142643375935439503360
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          128)
                        256))
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2662360355418534692364223966433247232
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
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2659916958886594780192839071004884992
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2668840585286901401064675113219129344
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          51922968585348276285304963292200960
                          51922968585348276285304963292200960)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          51922968585348276285304963292200960
                          51922968585348276285304963292200960)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          51922968585348276285304963292200960
                          51922968585348276285304963292200960)
                        256))
                    2048)))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            255880293552445008480539468949838888960
                            255880293552445008480539468949838888960)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1267650600228229401496703205376
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        70368744177664
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        72057594037927936
                        512)
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            3894222643901120721397872246915072
                            3898025595701805625775144470315008)
                          (Code.joinWords 128
                            3909434451103859474215832685379584
                            15211807202752587876015720628224))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1267650600228229401496703205376
                          128)
                        512)
                      1024))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1099511627776
                        128)
                      512)
                    1024)))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      2535301200456458802993406410752
                      256)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      140737488355328
                      256)
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
                        256))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2693757525484987478180494311424
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2233382993920
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          34359738368
                          128)
                        256))
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
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          51922968585348276285304963292200960
                          10384593717069655257060992658440192)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          51922968585348276357362557330128896
                          10384593717069655257060992658440192)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          51922968585348276285304963292200960
                          10384593717069655257060992658440192)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          51922968585348276285304963292200960
                          10384593717069655257060992658440192)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          51922968585348276285304963292200960
                          2251799813685248)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          51922968585348276285304963292200960
                          2251799813685248)
                        256))
                    2048)))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        158456325028528675187087900672
                        256)
                      (Nat.shiftLeft
                        633825300114114700748351602688
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        218076468058462760398280845827244032
                        256)
                      (Nat.shiftLeft
                        51922968585348276285304963292200960
                        256)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 2048
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        257874145687327184115730391513885048832
                        128)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          265849655638903904914846201506326118400
                          128)
                        256))
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1298074214633706907132624082305024
                      128)
                    1024))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          170209981393844818197765332792246272
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          167462348717850130970021228594593792
                          128)
                        256)
                      1024))
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
                          176538093190184139370036875193483264
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          41357100832445984223829942075392
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          792281625142643375935439503360
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256)
                        512)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          259203414247931307291975046468667965440
                          128)
                        (Nat.shiftLeft
                          271166648751681983013143125536452640768
                          128))
                      512)
                    1024)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        20282409603651670423947251286016
                        128)
                      512)
                    1024))
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256)
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256)
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256)
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256))))
                  4096))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      2535301200456458802993406410752
                      256)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        176538093190184139370036875193483264
                        256)
                      (Nat.shiftLeft
                        10384593717069655257060992658440192
                        256)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        3894222643901120721397872246915072
                        128)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1318356624237358577556571333591040
                        128)
                      1024))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        3904363848702946556609845872558080
                        40564819207303340847894502572032)
                      256)
                    512))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          171224101874027401718962695356547072
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          168476469198032714491218591158894592
                          128)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            158456325028528675187087900672
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10387287474595140244539173152751616
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          176540786947709624357515055687794688
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10387287474595140244539173152751616
                          128)
                        256))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        158456325028528675187087900672
                        128)
                      256)
                    512)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014718988379809510964925304678645760
                            319014718988379809510964925304678645760)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016)
                          256)
                        512))
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1331429271052212193259717758564696064
                            40564819207303340847894502572032)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329227995784915872903807077460213760
                            20282409603651670423947251286016)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Nat.shiftLeft
                          1349997500131705240548462913717796864
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Nat.shiftLeft
                          20789786756393019315079800688738304
                          256)))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          128)
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          128)))
                    1024)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            40723275532331869523098770341888
                            158456325028528675187087900672)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        (Nat.shiftLeft
                          20282409603651670423964431155200
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256)
                        512))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      2596148429267413814265248164610048
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      2596148429267413814265248164610048
                      1024)
                    (Nat.shiftLeft
                      2824609491042946229920590003095732224
                      1024)))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        256)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          43258576732788328326074996883456
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          176538093190184139370036875193483264
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)))))
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            4076764330333985755213397508489216
                            128)
                          (Nat.shiftLeft
                            168638094649561813739909420817580032
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1318356624237358577556571333591040
                            128)
                          (Nat.shiftLeft
                            178861062915102369748279583817334784
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            40723275532331869523081590472704
                            128)
                          256)
                        512)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          128)
                        (Nat.shiftLeft
                          10387287474595140244539173152751616
                          128)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          176540786947709624357515055687794688
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          166153499473114484112975882535043072
                          128)
                        (Nat.shiftLeft
                          2693757525484987478180494311424
                          128)))))
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          43258576732788328326074996883456
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2668840585286901401064675113219129344
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2693757525484987478180494311424
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        40723275532331869523081590472704
                        128)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          3905631499303174786011342575763456
                          (Code.joinWords 128
                            2660902557228272228552502757747064832
                            20282409603651670423947251286016))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2693757525484987478180494311424
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          1267650600228229401496703205376
                          10425316992601987126584074248912896)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          1299341865233935136534120785510400
                          (Code.joinWords 128
                            2671277643565840172089052525131464704
                            20282409603651670423947251286016))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2668881308562433732934198194809602048
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          2658455991569831745807614120560689152
                          40723275532331869523081590472704)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21550060203879899825443954491392
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            21550060203879899825443954491392)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2693757525484987478180494311424
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2693757525484987478180494311424
                            128)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376))
                        512)))
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          40723275532331869523081590472704
                          40723275532331869523081590472704)
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          128)
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          128))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      2596148429267413814265248164610048
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      166153499473114484112975882535043072
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          128)
                        256)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2693757525484987478180494311424
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          176538093190184139370036875193483264
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          128)
                        256)))))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        1949646623151016819501929529868288
                        40564819207303340847894502572032)
                      256)
                    512)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            4076764330333985755213397508489216
                            128)
                          (Nat.shiftLeft
                            168638094649561813739909420817580032
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1318356624237358577556571333591040
                            128)
                          (Nat.shiftLeft
                            178861062915102369748279583817334784
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            158456325028528675187087900672
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10387287474595140244539173152751616
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          176540786947709624357515055687794688
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          166153499473114484112975882535043072
                          128)
                        (Nat.shiftLeft
                          2693757525484987478180494311424
                          128)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2693757525484987478180494311424
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      2596148429267413814265248164610048
                      256)
                    512))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2693757525484987478180494311424
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        158456325028528675187087900672
                        128)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          72057594037927936
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          1267650600228229401496703205376
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016))
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2693757525484987478180494311424
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2693757525484987478180494311424
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        (Code.joinWords 256
                          1267650600228229401496703205376
                          20282409603651670423947251286016))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1331421665148610823883167491101294592
                            40723275532331869523081590472704)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016)
                          256)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        (Code.joinWords 256
                          1329227995784915872903807060280344576
                          20282409603651670423947251286016)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21550060203879899825443954491392
                            128)
                          (Code.joinWords 128
                            21550060203879899825443954491392
                            1267650600228229401496703205376)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2693757525484987478180494311424
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2693757525484987478180494311424
                            128)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376))
                        512)))
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          40723275532331869523081590472704
                          2199023255552)
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        20282409603651670423947251286016
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20282409603651670423947251286016
                          1099511627776)
                        256))))))))))
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            265845599156984081348913099322788151296
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            265845599156984081422700075617626357760
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            265849655638903904914846201506326118400
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            265849655638903904914846201506326118400
                            128)
                          256)))
                    2048)
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
                            271166648751681983013143125536452640768
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271162511199558467067910269042444730368
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271162511199558467067910269042444730368
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            15954873620414671105510509679761948672
                            128)
                          256)
                        (Nat.shiftLeft
                          255211775190761876036872457774212055040
                          128)))))
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          59440464698812087261953261568
                          297747071055821155530452781502797185024)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          59459807511925921328748560384
                          297747071055821155530452781502797185024)
                        256))
                    (Nat.shiftLeft
                      59421121885698253195157962752
                      256))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          297747071055821155530452781502797185024
                          256)
                        (Nat.shiftLeft
                          41538374868278621028243970633760768
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          298910145552132956919243612680542486528
                          256)
                        (Nat.shiftLeft
                          41538374868278621028243970633760768
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            139402786127287037183881894908047392768
                            20769187434139310514121985316880384)
                          256)
                        (Nat.shiftLeft
                          41538374868278621028243970633760768
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            139402786127287037183881894908047392768
                            20769504346789367571472359492681728)
                          256)
                        (Nat.shiftLeft
                          41538374868278621028243970633760768
                          256))))))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        604462909807314587353088
                        256)
                      (Nat.shiftLeft
                        604462909807314587353088
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        256)
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
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
                            271162511140122838072376640297190293504
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            271166405362766739193098038169437208576
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          73786976294838206464
                          128)
                        256)
                      1024))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4835703278458516698824704
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4835703278458516698824704
                          128)
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      19807040628566084398385987584
                      256)
                    (Nat.shiftLeft
                      19826383441679918465181286400
                      256))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          98362871688083774594881722460745498624
                          256)
                        (Nat.shiftLeft
                          41538374868278621028243970633760768
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          99525946184395575983672553638490800128
                          256)
                        (Nat.shiftLeft
                          41538374868278621028243970633760768
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            99525946204221959425352472103672086528
                            20769187434139310514121985316880384)
                          256)
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            99525946204221959425352472103672086528
                            20769504346789367571472359492681728)
                          256)
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256))))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        906694364710971881029632
                        128)
                      256)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        211106232532992
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769187434139310514121985316880384
                            128)
                          256)
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
                            128)
                          256)
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        297747071055821155530452781502797185024
                        297747071055821155530452781502797185024)
                      256)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        297747071055821155530452781502797185024
                        297747071055821155530452781502797185024)
                      256))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19342813113834066795298816
                            20769187434139310514121985316880384)
                          256)
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19342813113834066795298816
                            20769504346789367571472359492681728)
                          256)
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          256)))
                    2048)))
              16384)
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        297747071055821155530452781502797185024
                        297747071055821155530452781502797185024)
                      256)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        297747071055821155530452781502797185024
                        297747071055821155530452781502797185024)
                      256))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            72057594037927936
                            20769187434139310514121985316880384)
                          256)
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            72057594037927936
                            20769504346789367571472359492681728)
                          256)
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          256)))
                    2048))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769187434139310514121985316880384
                            128)
                          256)
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
                            128)
                          256)
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          256)))
                    2048)
                  4096))
              16384)))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        3894222643901120721397872246915072
                        512)
                      1024)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4056481920730334084789450257203200
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2535301200456458802993406410752
                          128)
                        256)))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1299341865233935136534120785510400
                      512)
                    1024))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            319014719047858959821953449862826557440
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            319014719047858959821953449862826557440
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            83076749736557242056487941267521536
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85201965968784415731647388072280064
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            83076749736557315843464236105728000
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749755900055170322008062820352)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          103846254107525126020252884254326784)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          20770772021568112193166439690010624)
                        256)))))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      40564819207303340847894502572032
                      256)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        2668840585286901401064675113219129344
                        256)
                      (Nat.shiftLeft
                        10384593717069655257060992658440192
                        256))
                    2048))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        158456325028528675187087900672
                        128)
                      256)
                    512)
                  2048))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2663336446380710429003376427901386752
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            158456325028528675187087900672
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10425316992601987126584074248912896
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2660893049848770516831991532473024512
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2668881308562433732934198194809602048
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10425316992601987126584074248912896
                          256)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2693757525558774454475332517888
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            158456325028528675187087900672
                            128)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600302016377791541411840)
                        256)))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504351625070849930876191506432
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504351625070849930876191506432
                          128)
                        256))
                    2048)))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          255211775190703847597530955573826158592
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014718988379809496913694467282698240
                          319014718988379809496913694467282698240)
                        256))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4072327553233186952308159047270400
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2535301200456458802993406410752
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        70385924046848
                        256)
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504351625070849930876191506432
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625070849930876191506432
                            128)
                          256)
                        72057594037927936))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014719047800931382611947662440660992
                            63802943857155112224422494289000398848)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13835058055282950144
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            85201965968784415731647388072280064)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557315843464236105728000)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)
                          256))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749755900055170322008062820352)
                          256)
                        (Nat.shiftLeft
                          1099511627776
                          128))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          103845937170696552570609926584401920
                          83077066673385815506130898937446400)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          103845937170696552570609926584401920
                          1584587428801679044454373130240)
                        256)))))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    140737488355328
                    256)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      2199023255552
                      128)
                    256)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      72057594037927936
                      256)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2693757525484987478180494311424
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256)))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        20769504346789367643529953530609664
                        256)
                      (Nat.shiftLeft
                        20769504346789367571472359492681728
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          262144
                          128)
                        256)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            262144
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2693757525484987478180494311424
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            158456325028528675187087900672
                            128)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)
                        256)))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20769504346789367571472359492681728
                          1125899906842624)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20769504346789367571472359492681728
                          1125899906842624)
                        256))
                    2048)))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      604462909807314587353088
                      256)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      40564819207303340847894502572032
                      256)
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
                        512))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            265849655638903904914846201506326118400
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            265849655638903904914846201506326118400
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        302231454903657293676544
                        128)
                      256))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        20282409603651670423947251286016
                        128)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        19342813113834066795298816
                        128)
                      1024)))
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256)
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          51922968604691089399139030087499776
                          256)
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256)
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256))))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          737869762948382064640
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          147573952589676412928
                          256)
                        512))
                    2048)
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          256)
                        512))
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
                        512))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3894222643901120721397872246915072
                            128)
                          (Nat.shiftLeft
                            4137611559144940766485239262347264
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3955069930740515074171914386669568
                            128)
                          (Nat.shiftLeft
                            243448336365705743340562173394944
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          295147905179352825856
                          128)
                        512)
                      1024))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        20282409603651670423947251286016
                        128)
                      512)
                    1024))
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256)
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256)
                        (Nat.shiftLeft
                          9671406556917033397649408
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          51922968585348276285304963292200960
                          256)
                        (Nat.shiftLeft
                          9671406556917033397649408
                          256))))
                  4096))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    604462909807314587353088
                    256)
                  2048)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          319014718988379809496913694467282698240
                          128)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          255211775190703847597530955573826158592
                          319014718988379809496913694467282698240)
                        256))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        302305241879952131883008
                        128)
                      256))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4148386589246880716397961239592960
                          40564819207303340847894502572032)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          19342813113834066795298816
                          128)
                        (Nat.shiftLeft
                          20769504346789367572598259399524352
                          256)))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    19342813113834066795298816
                    256)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          40723275532331869523081590472704
                          158456325028528675187087900672)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        20769504366132180685306426287980544
                        256)
                      (Nat.shiftLeft
                        20769504346789367571472359492681728
                        256))))))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        590295810358705651712
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        158456325028528675187087900672
                        128)
                      256)
                    512))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          319014718988379809510748752522564861952
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            63802943797675961913433969730852487168
                            59421121885698253195158749184)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016)
                          256)))
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            295147905179352825856
                            128)
                          1329227995784915872975864654318272512))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1331429271052212193259717758564696064
                            40564819207303340847894502572032)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329227995784915872903807077460213760
                            20282409603651670423947251286016)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1349997183219055183417929045597224960
                          256)
                        (Nat.shiftLeft
                          1329228312697565930034340928400916480
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1349997183219055183417929045597224960
                          256)
                        (Nat.shiftLeft
                          20599322253708800957815371857920
                          256)))))
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        262144
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          128)
                        (Code.joinWords 128
                          262144
                          20282409603651670423947251286016))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            40723275532331869523081590472704
                            158456325028528675187087900672)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          256)
                        (Nat.shiftLeft
                          4835703278458516698824704
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          256)
                        (Nat.shiftLeft
                          4835703278458516698824704
                          256)))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      2596148429267413814265248164610048
                      1024)
                    (Nat.shiftLeft
                      2658455991569831745807614120560689152
                      1024))
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2596148429267413814265248164610048
                        128)
                      256)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      40723275532331869523081590472704
                      128)
                    256)))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1987676141157863701546830626029568
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2535301200456458802993406410752
                        128)
                      256))
                  2048)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          19342813113834066795298816
                          128)
                        256)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Nat.shiftLeft
                            83076749736557242056487941267521536
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            85080271510520263867433432815501312
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2693757525484987478180494311424
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            83076749736557242056487941267521536
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1267650600228229401496703205376
                            128)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            40723275532331869523081590472704
                            40723275532331869523081590472704)
                          256)
                        512)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          128)
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749755900055170322008062820352)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          83076749736557242056487941267521536
                          128)
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512))
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2668840585286901401064675113219129344
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10384593717069655257060992658440192
                          256)
                        512))))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        40723275532331869523081590472704
                        128)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          256)
                        (Code.joinWords 256
                          3905631499303174786011342575763456
                          (Code.joinWords 128
                            2660902557228272228552502757747064832
                            20282409603651670423947251286016)))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            158456325028528675187087900672
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          10425316992601987126584074248912896
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          256)
                        (Code.joinWords 256
                          1299341865233935136534120785510400
                          (Code.joinWords 128
                            2671277643565840172089052525131464704
                            20282409603651670423947251286016)))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2668881308562433732934198194809602048
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          2658455991569831745807614120560689152
                          40723275532331869523081590472704)
                        512))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21550060203879899825443954491392
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21550060203879899825443954491392
                            128)
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            20282409603651670423947251286016)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2693757525484987478180494311424
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            590295810358705651712
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            295147905179352825856
                            128)
                          256))))
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          40723275532331869523081590472704
                          40723275532331869523081590472704)
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          128)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          128)
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          128))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2596148429267413814265248164610048
                        128)
                      256)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      158456325028528675187087900672
                      128)
                    256))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2003521773660716569065539416096768
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2535301200456458802993406410752
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        2193669363694950979290044896903168
                        40564819207303340847894502572032)
                      256)
                    512))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          19342813113834066795298816
                          128)
                        256)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20282409603651670423947251286016
                            128)
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            85080271510520263867433432815501312)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2693757525484987478180494311424
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            40723275532331869523081590472704
                            158456325028528675187087900672)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749755900055170322008062820352)
                        256)
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          83076749736557242056487941267521536
                          128)
                        (Code.joinWords 128
                          1267650600228229401496703205376
                          1267650600228229401496703205376)))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        158456325028528675187087900672
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      2596148429267413814265248164610048
                      256)
                    512))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          158456325028528675187087900672
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        158456325028528675187087900672
                        128)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          72057594037927936
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016)
                          256)
                        (Code.joinWords 256
                          1267650600228229401496703205376
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2693757525484987478180494311424
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            158456325028528675187087900672
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1331421665148610823883167491101294592
                            40723275532331869523081590472704)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1329227995784915872903807060280344576
                            20282409603651670423947251286016)
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          256)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          20282409603651670423947251286016
                          256)
                        (Code.joinWords 256
                          1329227995784915872903807060280344576
                          20282409603651670423947251286016)))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            21550060203879899825443954491392
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            21550060203879899825443954491392
                            128)
                          21550060203879899825443954491392))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2693757525484987478180494311424
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            590295810358705651712
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1267650600228229401496703205376
                            1267650600228229401496703205376)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            295147905179352825856
                            128)
                          256))))
                  (Code.joinWords 1024
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          40723275532331869523081590472704
                          2199023255552)
                        256)
                      512)
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        20282409603651670423947251286016
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          20282409603651670423947251286016
                          1099511627776)
                        256)))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (256 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage004
