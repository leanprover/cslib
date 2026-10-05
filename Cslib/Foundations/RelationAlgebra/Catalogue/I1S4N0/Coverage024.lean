/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 1537–1600 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage024

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            33554432
                            128)
                          (Code.joinWords 128
                            807403520
                            255880293552445008480539468950646292480))
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
                            3723548340384804883547553792
                            128)
                          (Code.joinWords 128
                            255876389188596305533982859103966330880
                            255876389188596305533982859103966330880))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          9223372039002259456
                          128)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            50462720
                            128)
                          (Code.joinWords 128
                            255880293552445008480539468949838888960
                            255880293552445008480539468949838888960)))
                      1024))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
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
                        (Code.joinWords 256
                          (Code.joinWords 128
                            255880293552445008480684147087868166144
                            255880293552445008480756204681906094080)
                          85739110091975776762723463742244257792)
                        512)
                      1024))
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          3904363848702946556609845872558080
                          3904363848702946773347785552953344)
                        (Code.joinWords 128
                          3904363848702960427908354162032640
                          1308215419435546613643105997422592))
                      512)
                    1024)
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        140737488355328
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          212676479325586539664609129644855132160
                          2658455991569831745807614120560689152)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        140737488355328
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          212676479325586539664609129644855132160
                          2658455991569831745807614120560689152)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          212676479325586539664609129644855132160
                          2658455991569831745807614120560689152)
                        256))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3094850098213450687247843328
                            128)
                          (Code.joinWords 128
                            140737488355328
                            10995116277760))
                        (Nat.shiftLeft
                          309485009821345068724781056
                          128))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          212676479325586539664609129644855132160
                          2658455991569831745807614120560689152)
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            3094850098213450687247843328
                            128)
                          (Code.joinWords 128
                            140737488355328
                            8796093022208))
                        (Nat.shiftLeft
                          37926505815546838122496
                          128))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            3094850098213450687247845376)
                          (Code.joinWords 128
                            140737488355328
                            10995116277760))
                        (Nat.shiftLeft
                          309485009821345068724781056
                          128)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          212676479325586539664609129644855132160
                          2658455991569831745807614120560689152)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          212676479325586539664609129644855132160
                          2658455991569831745807614120560689152)
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          32768
                          223310303291865866647839586127097888768)
                        (Code.joinWords 128
                          225968759283435698405176415293727047680
                          2658455991569831746528190060939968512))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 256
                        (Code.joinWords 128
                          32768
                          223310303291865866647839586127097888768)
                        (Code.joinWords 128
                          225968759283435698405176415293727047680
                          2658455991569831746528190060939968512))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          32768
                          223310303291865866647839586127097888768)
                        (Code.joinWords 128
                          55827575822966466673489111577842941952
                          2658455991569831746528190060939968512)))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          212676479325586539664609129644855164928
                          223310303291865866647839586127097888768)
                        (Code.joinWords 128
                          13292279957849158729038070602803445760
                          2658455991569831746528190060939968512))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 256
                        (Code.joinWords 128
                          212676479325586539664609129644855164928
                          223310303291865866647839586127097888768)
                        (Code.joinWords 128
                          13292279957849158729038070602803445760
                          2658455991569831746528190060939968512))
                      (Code.joinWords 256
                        (Code.joinWords 128
                          212676479325586539664609129644855164928
                          223310303291865866647839586127097888768)
                        (Code.joinWords 128
                          13292279957849158729038070602803445760
                          720575940379279360)))
                    2048)))))
          65536)
        131072)
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      2596148429267413814265248164610048
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          45196348005116407092543705299843809280
                          (Nat.shiftLeft
                            570425344
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            16777216
                            128)
                          256))
                      1024))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2661214399275928372985270946735587328
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2661214399275928372985270946735587328
                          128)
                        256)
                      1024))
                  4096))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          32768
                          45196510264393236305907096875706613760)
                        (Nat.shiftLeft
                          2661904001202452541885360951651205120
                          128))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          32768
                          45193751856687139678729440049531715584)
                        (Nat.shiftLeft
                          2659145593496355914707853659057684480
                          128))
                      1024))
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        2606289634069239649477221790253056
                        633825300114114700748351602688)
                      256)
                    512)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128))
                        512)
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        32768
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2769182736198567127710835396313088
                            633825944717139621285376032768)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009893402662762708992
                            128)
                          256)
                        512))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        512)
                      1024))))))
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
                          42537892013546575346736091179283120128
                          (Nat.shiftLeft
                            570425344
                            128))
                        (Nat.shiftLeft
                          538968064
                          256))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2661214399275928372985270946735587328
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2661214399275928372985270946735587328
                          128)
                        256)
                      1024))
                  4096))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          32768
                          45196510264393236305907096875706613760)
                        (Nat.shiftLeft
                          2661904001202452541885360951651205120
                          128))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          32768
                          45193751856687139678729440049531715584)
                        (Nat.shiftLeft
                          2659145593496355914707853659057684480
                          128))
                      1024))
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        168759789107183723762453104325296128
                        256)
                      512)
                    1024)
                  2048)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        168759789107183723762453104325296128
                        256)
                      512)
                    1024)
                  2048))
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      32768
                      (Code.joinWords 256
                        42704055654224491656684279033296322560
                        169411411188045110000705940100218880))
                    1024)
                  2048)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      32768
                      (Code.joinWords 256
                        42701449364590422417034801811506069504
                        166805121554582694444277467719925760))
                    1024)
                  2048))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      2596148429267413814265248164610048
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          45196348005116407092543705300380712960
                          (Nat.shiftLeft
                            570425344
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            16777216
                            128)
                          256))
                      1024))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2661214399275928372985270946735587328
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2661214399275928372985270946735587328
                          128)
                        256)
                      1024))
                  4096))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          32768
                          45196510264393236305907096875706613760)
                        (Nat.shiftLeft
                          2659307852773185128071095703486595072
                          128))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          32768
                          45193751856687139678729440049531715584)
                        (Nat.shiftLeft
                          689601926524168900239538496995328
                          128))
                      1024))
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        2606289634069239649477221790253056
                        633825300114114700748351602688)
                      256)
                    512)
                  4096)
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128))
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128))
                        512)
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        32768
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            162893102736151571141075771850752
                            633825944717139621285376032768)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009893402662762708992
                            128)
                          256)
                        512))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        512)
                      1024)))))))))
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    140737488355328
                    256)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769187434139310514121985316880384
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          72057594037927936
                          128)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            19342813113834066795298816
                            19342813185891660833226752)
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
                            128))))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769187434139310514121985316880384
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
                            128)
                          256)
                        512))
                    2048)
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    604462909807314587353088
                    256)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      604462909807314587353088
                      256)
                    2048)
                  (Nat.shiftLeft
                    140737488355328
                    256)))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769187434139310514121985316880384
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
                            128)
                          256)
                        512))
                    2048)
                  4096)
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
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769187434139310514121985316880384
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
                            128)
                          256)
                        512))
                    2048)))))
          65536)
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    2596148429267413814265248164610048
                    1024)
                  2048)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      42704045513019689830849067061818163200
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          538968064
                          1048576)
                        256))
                    1024)
                  2048))
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            83076749736557242056487941267521536
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            83076749736557242056487941267521536
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            83076749736557242056487941267521536
                            128)
                          (Nat.shiftLeft
                            83076749755900055170322008062820352
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            83076749736557242056487941267521536
                            128)
                          (Nat.shiftLeft
                            83076749755900055170322008062820352
                            128))
                        512)
                      1024)))
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          168759789107183723762453104325296128
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          168759789107183723762453104325296128
                          256)
                        512)
                      1024)
                    2048))
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2758407706096627177656826174898176
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        633825300114114700748351602688
                        128)
                      256))
                  2048))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        32768
                        (Code.joinWords 256
                          42704055654224491656684279033296322560
                          169411411188045110000705940100218880))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        32768
                        (Code.joinWords 256
                          42701449364590422417034801811506069504
                          166805121554582694444277467719925760))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            83076749736557242056487941267521536
                            128)
                          (Nat.shiftLeft
                            83076749755900055170322008062820352
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            2769182736840808969239819901206528
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            633825302622872044856187813888
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            19342813118337666422669312
                            128)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4503599627370496
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4503599627370496
                            128)
                          256)
                        512)
                      1024))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            16777216
                            128)
                          (Code.joinWords 128
                            1048576
                            1048576))
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            32768
                            128)
                          (Code.joinWords 128
                            140737488355328
                            8830452760576))
                        (Nat.shiftLeft
                          4873629784274063536947200
                          128))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          4835777065434811553808384
                          128)
                        512))
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          16777216
                          128)
                        (Nat.shiftLeft
                          16777216
                          128))
                      1024))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769187438975013793706401922547712
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          72057594037927936
                          128)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            72057594037927936
                            128)
                          (Nat.shiftLeft
                            20769504351625144638033088116424704
                            128))))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          72057594037927936
                          128)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            72057594037927936
                            128)
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267783684)))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          72057594037927936
                          128)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242128545535305449472)
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            83076749755900055170322008062820352)))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769187438975013793706401922547712
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            316936828647237745169594843136))
                        512))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2758407706096627177656826174898176
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        633825300114114700748351602688
                        128)
                      256))
                  2048)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          4332790137498830962146934784
                          128)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            4332790137498830962147459072
                            128)
                          (Code.joinWords 128
                            297747071055821155530452781502797185024
                            297747071055821155530452781502797185024)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          309485009821345068724781056
                          128)
                        (Nat.shiftLeft
                          309485009821345068725043200
                          128)))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2758407706096627177656826174898176
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          633825300114114700748351602688
                          128)
                        256)))
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Code.joinWords 128
                          32768
                          34816)
                        (Code.joinWords 128
                          140737488355328
                          8830452760576))
                      (Nat.shiftLeft
                        4873629784274063536947200
                        128))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        309485009821345068724781056
                        128)
                      (Nat.shiftLeft
                        314320786886779880261812224
                        128)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        32768
                        (Nat.shiftLeft
                          2769182736840808969239819901206528
                          128))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          633825302622872044856187813888
                          128)
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769187434139310514121985316880384
                            128)
                          (Nat.shiftLeft
                            1125899906842624
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
                            128)
                          (Nat.shiftLeft
                            1125917086711808
                            128))
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            297747071125145797746574977961643999232
                            127605887664676566014887674245760548864)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            16140901064495857664
                            16140901064496775168)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            83076749755900055170322008063082500))
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            173034307573395154974571736596480
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            633825302622872044856187813888
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19342813118337666422669312
                            19342813118337666422669312)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4503599627370496
                            4503599627370496)
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769187434139310514121985316880384
                            128)
                          (Nat.shiftLeft
                            1125899906842624
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
                            128)
                          (Code.joinWords 128
                            4503599627370496
                            5629516714082304))
                        512)))))))))
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            838860800
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2097152
                            128)
                          (Nat.shiftLeft
                            265849655638903904914846201507164979200
                            128)))
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        604462909807314587353088
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        604462909807314587353088
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          256)
                        (Nat.shiftLeft
                          166153499473114484112975882535043072
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          256)
                        (Nat.shiftLeft
                          166153499473114484112975882535043072
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          256)
                        (Nat.shiftLeft
                          166153499473114484112975882535043072
                          256))))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
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
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            265849655638945008392713098898266128384
                            128)
                          (Nat.shiftLeft
                            95708472240332619620724485464440963072
                            128))
                        (Nat.shiftLeft
                          265849655638964351205826932965061427200
                          128))
                      1024)
                    2048))
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          213507246872469713656589220053495316480)
                        (Code.joinWords 256
                          213341093323478997601061033174995304448
                          166153499666542615251316550488031232))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          213507246872469713656589220053495316480)
                        (Code.joinWords 256
                          213341093323478997601061033174995304448
                          166153499666542615251316550488031232))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          43366063412000481924901916337611210752)
                        (Code.joinWords 256
                          213341093323478997601061033174995304448
                          166153499666542615251316550488031232))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            265845599156983174580761412056068915200
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            56295854337687552
                            128)
                          (Nat.shiftLeft
                            265845599156983174580761412056068915200
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            265849655638903904914846201506326118400
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            39614081257132168798919458816
                            3276800)
                          (Nat.shiftLeft
                            265849655638903904914846201506326118400
                            128)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          604462909807314587353088
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            45035996273737728
                            4503599627370496)
                          2951479051793528258560))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          604462909807314587353088
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            45035996273737728
                            584115552256)
                          2361183241434822606848))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          604462909807314587353088)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            45035996273737856
                            4503599627370496)
                          2951479051793528258560))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          256)
                        (Nat.shiftLeft
                          166153499473114484112975882535043072
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          256)
                        (Nat.shiftLeft
                          166153499473114484112975882535043072
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          212676479325586539664609129644855132160
                          256)
                        (Nat.shiftLeft
                          166153499473114484112975882535043072
                          256))))))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          4056481920730334084789450257203200
                          128)
                        (Nat.shiftLeft
                          4056543818676771650377124256153600
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          4056481981177252254819415117266944
                          128)
                        (Nat.shiftLeft
                          1460395389409357836111876091543552
                          128)))
                    1024)
                  2048)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          212676479325586539664609129644855164928
                          830767497365572420564879412675215360)
                        (Code.joinWords 256
                          213341093323478997601061033174995304448
                          166153499666542615251316550488031232))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          212676479325586539664609129644855164928
                          830767497365572420564879412675215360)
                        (Code.joinWords 256
                          213341093323478997601061033174995304448
                          166153499666542615251316550488031232))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          212676479325586539664609129644855164928
                          830767497365572420564879412675215360)
                        (Code.joinWords 256
                          213341093323478997601061033174995304448
                          193428131138340667952988160))))
                  4096))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            16777216
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1048576
                            128)
                          (Nat.shiftLeft
                            16777216
                            128)))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        2606289634069239649477221790253056
                        633825300114114700748351602688)
                      256)
                    512)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769187438975013793706401922547712
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            19342813113834066795298816
                            19342813113834066795298816)
                          (Nat.shiftLeft
                            20769504351625144638033088116424704
                            128))
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 512
                      32768
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2769182736198567127710835396313088
                          633825944717139621285376032768)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769187434139310514121985316880384
                            128)
                          (Nat.shiftLeft
                            4835703278458516698824704
                            128))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
                            128)
                          (Nat.shiftLeft
                            4835777065434811537031168
                            128))
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          604462909807314587353088
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32768
                            1126484022394880)
                          2508757194024499019776))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1125917087760384
                          128)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          1048576
                          1048576)
                        512)
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            297747071055821155530452781502797185024
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            63050394783186944
                            63050394783711232)
                          (Nat.shiftLeft
                            297747071055821155530452781502797185024
                            128)))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4503599627370496
                          4503599627632640)
                        512))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          604462909807314587353088)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            32896
                            1126484022394880)
                          2508757194024499019776))
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          4503599627370496
                          5629516714082304)
                        512)))
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        2606289634069239649477221790253056
                        633825300114114700748351602688)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            19342813113834066795298816
                            19342813113834066795298816)
                          (Nat.shiftLeft
                            1329227995784915872903807060280606724
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            19342813113834066795298816
                            1329227995804258686017641127075643392)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769187438975013793706401922547712
                            128)
                          256)
                        512)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            316917485834195968696837472256
                            128))))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            297747071125145797746574977961643999232
                            69324642199981295394350956544)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            127605887664676566014887674245760548864
                            69324642199981295394351874048)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318534660
                            128))))
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        32768
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            173034306931153313445587231703040
                            633825944717139621285376032768)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009893402662762708992
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009893402662762708992
                            128)
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769187434139310514121985316880384
                            128)
                          (Nat.shiftLeft
                            4835703278458516698824704
                            128))
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
                            128)
                          (Nat.shiftLeft
                            314320786886779880261812224
                            128))))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 4096
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    2596148429267413814265248164610048
                    1024)
                  2048)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      42704045513019689830849067062355066880
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          538968064
                          1048576)
                        256))
                    1024)
                  2048))
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            83076749736557242056487941267521536
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            83076749736557242056487941267521536
                            128)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            83076749736557242056487941267521536
                            128)
                          (Nat.shiftLeft
                            4503599627370496
                            128))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            83076749736557242056487941267521536
                            128)
                          (Nat.shiftLeft
                            4503599627370496
                            128))
                        512)
                      1024)))
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          168759789107183723762453104325296128
                          256)
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          168759789107183723762453104325296128
                          256)
                        512)
                      1024)
                    2048))
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2758407706096627177656826174898176
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        633825300114114700748351602688
                        128)
                      256))
                  2048))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        32768
                        (Code.joinWords 256
                          42704055654224491656684279033296322560
                          166815262758777696186440691935608832))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        32768
                        (Code.joinWords 256
                          42701449364590422417034801811506069504
                          651622081468210331301585184882688))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            83076749736557242056487941267521536
                            128)
                          (Nat.shiftLeft
                            83076749755900055170322008062820352
                            128))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            10775030101939950062255558623232
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            633825302622872044856187813888
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            19342813118337666422669312
                            128)
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4503599627370496
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4503599627370496
                            128)
                          256)
                        512)
                      1024))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            16777216
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            1048576
                            17825792)
                          256))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        2606289634069239649477221790253056
                        633825300114114700748351602688)
                      256)
                    512)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          128)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769504346789367571472359492681728
                          128)
                        512))
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        32768
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            162893102736151571141075771850752
                            633825944717139621285376032768)
                          256))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            4503599627370496
                            4503599627370496))
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          128)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            103846254083346609627960300760203264)
                          (Code.joinWords 128
                            4503599627370496
                            4503599627370496))
                        512))))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 512
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        2758407706096627177656826174898176
                        128)
                      256)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        633825300114114700748351602688
                        128)
                      256))
                  2048)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            297747071055821155530452781502797185024
                            297747071055821155530452781502797185024)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            950272
                            128)
                          (Code.joinWords 128
                            297747071055821155530452781502797185024
                            297747071055821155530452781502797217792)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          262148
                          128)
                        512))
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2758407706096627177656826174898176
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          633825300114114700748351602688
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          2606289634069239649477221790253056
                          633825300114114700748351602688)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          65536
                          128)
                        512)
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            10775030101939950062255558623232
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            633825302622872044856187813888
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          256))
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          128)
                        512)
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1349997500131705240475279419773026304
                            128)
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128))))))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            1412304745521473114960295001547866112)
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            19342813185891660833226752)))
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Nat.shiftLeft
                            10775030101939950062255558623232
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2508757344107836211200
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            19342813118337666422669312
                            328827822939682735147450368)
                          256))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        32768
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            162893102736151571141075771850752
                            644603024920537024430080)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009893402662762708992
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            4503599627370496
                            309485009897906262390079488)
                          256)))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          20769187434139310514121985316880384
                          128)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            309485009821345068724781056
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            20769504346789367571472359492747264
                            128)
                          (Code.joinWords 128
                            4503599627370496
                            309485009825848668352151552)))))))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (1536 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage024
