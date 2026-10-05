/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 2753–2816 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage043

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            226854218298297517543510253423426535424
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212679075523534013112748413203572064256
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            170805797458361689668283322434100264960
                            128)
                          (Code.joinWords 128
                            212679075523533408659062118663327842304
                            226854218981834454194071536909993115648)))
                      1024))
                  4096)
                8192)
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            32768
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            32768
                            170141183460469231731687303715884138496)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            604462909807314587353088
                            170141183460469231731687303715884105728)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            140737488355328
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256))
                      1024)))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            226854218298297517543510253423426535424
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
                            212679075513630492809994586050447540224
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            180775007426787244341145428331717591040
                            128)
                          (Code.joinWords 128
                            212679075474015807089952750676576567296
                            226854218971892248256010784774499074048)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            223313061699571963275017242953272786944
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213343699613113066840710510396785557504
                            226854218932122817657624954171778138112)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            225971517740660001055149875384385798144
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853162103782896238697275285569536
                            218087292800201226994793981132406784)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            225971517691141795032354072119901945856
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853112586181336352842062877425664
                            2710541853257309361820951930243907584)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            225971517740660001066679090432601751552
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            181481159799509295272397907698900926464
                            128)
                          (Code.joinWords 128
                            213509853162103782907768053060989878272
                            51923602604078883442172550891700224)))
                      1024))))))
          65536)
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 128
                          9223372036854775808
                          9223512774343131136)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      576460752303423488
                      1024))
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        35184372088832
                        128)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        720575940379279360
                        37383395344384)
                      1024))
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213341093323478997601061033174995304448
                            226851449749386619090497384623625994240)
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            225971517691141795020824857073833476096)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213341093323478997601061033174995304448
                            226854218298297517543510253423426535424)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10634635262663473050047414372294197248
                            665303599973724598156990271046287360)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            10634635262663473050623875124597620736
                            692137227724613253217199950135296)))
                      1024)))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183500083312988819472512656080896
                            180775007468838520050620689544697085952)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            212679075513629888335699678877867704320)
                          (Code.joinWords 128
                            213509843011150203261031115636829323264
                            226854208199347733215946631469753958400)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13293091254233304795855028492854886400
                            665263035154517294816142376543715328)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            13334629629101583417459733215792070656
                            649037107316853453566312041152512)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13293091254233304795855028492854886400
                            665303599973724598156990271046287360)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            144115188075855872
                            649037107316853453568511064408064)
                          (Code.joinWords 128
                            2699997535564610937985822585255886848
                            43100120407759799650887908982784)))
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            140737488355328
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170141183460469231731687303715884105728)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          830777638570374246400091386300858368
                          128)
                        256)
                      1024))
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          128
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            689601926524156794414206543724544)
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          35734127902720
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            831467240651640908105178127206973440)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            651572408517309912369305447563264
                            43258576732788328326074996883456)
                          256))
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            223310303291865866647839586127097888768
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            226851449749386619090497384623625994240
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            11298437964171784919682360012382928896
                            665273176359319120651354350169358336)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            10634635262663473050623875124597620736
                            649037107316853453566312041152512)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212676479325586539673832501681709907968
                            13295038365555255366015560218136543232)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213507246822952112094433409891404087296
                            2713148142891378599058743305240051712)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            11299259401760732812334529876060012544
                            830818203544324054651611815165820928)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            10633823966279326983230456482242756608
                            651572408517309912369305447563264)
                          (Code.joinWords 128
                            10634637797964673507082678118004031488
                            43100120407759799650887908982784)))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            11298610364653415958880963564018860032
                            664624139252002267197788038128205824)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            13333981225819566678120867652102520832
                            649037107316853453566312041152512)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13957715393330564558142143996620701696
                            665273176359319120687383147188322304)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            2700644037370727335124701091966484480
                            689601926524156794414206543724544)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13957715393330564558142143996620701696
                            831426675871119230991998366294999040)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            651572408517309912369305447563264
                            128)
                          (Code.joinWords 128
                            2700806296647556548343977481900916736
                            651572408517309912369305447563264)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          10633823966279326983230456482242756608
                          (Code.joinWords 128
                            13957715393330564558142143996620701696
                            830818203583009680915308745775382528))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            10633823966279326983230456482242756608
                            2535301200456458802993406410752)
                          (Code.joinWords 128
                            2699997535564610938129937773331742720
                            43258576732788328326074996883456)))
                      1024))))))
          65536))
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        39614081257132168796771975168
                        (Code.joinWords 256
                          39614685720041976111359328256
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      154742504910672534362390528
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            604462909807314587353088
                            170141183460469231731687303715884105728)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          13292442217125987942401462180813733888
                          256)
                        512)
                      1024)
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            223310303291865866647839586127097888768)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            226854218298297517543510253423426535424)
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            223310303291865866647839586127097888768
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            226851449749386619090497384623625994240
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            665273176204576615740681815806967808
                            665273176359319120651354350169358336)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            10634475538687844293719286539993743360
                            692137227724613253217199950135296)))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213341093323478997601061033174995304448
                            226851449749386619090497384623625994240)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212676479365200620921741298441627107328
                            225968759325525659729350129594228801536)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            833373826768465422257197965599834112
                            220845693049678816538039580058714112)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            11298437964171784919682360012382928896
                            665273176359319120651354350169358336)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            10634635262663473050623875124597620736
                            649037107316853453566312041152512)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            664613997892457936451903530140172288
                            128)
                          (Code.joinWords 128
                            11299259401760732812334529876060012544
                            665313741178526423992202244671930368))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          (Code.joinWords 128
                            13292444752427188399436725926523568128
                            43100120407759799650887908982784)))
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        151115727451828646838272
                        512)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        193428131138340667952988160
                        151706023262187352489984)
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2048
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          188894659314785808547840
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            651572408517309912369305447563264
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            689601926524156794414206543724544)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13293093789534505252890292238564720640
                            43258576732788328326074996883456)
                          256))
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            831426675677691099853657698342010880
                            872965050700712225792574203338162176)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            10634473003386643837260483546587332608
                            649037107316853453566312041152512)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075474015807078423394893019742208
                            128)
                          (Code.joinWords 128
                            170141183460469231740910675752738881536
                            225971355431864965817261298284981387264))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075474054492713874435063465246720
                            128)
                          (Code.joinWords 128
                            170805797458361689677398608079898017792
                            226854056081110649675688045865221488640)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            38685626227668133590597632
                            128)
                          (Code.joinWords 128
                            831426675677691099853657698342010880
                            207733073140643027507441030385369088))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107317443749376670746804224
                            128)
                          (Code.joinWords 128
                            10634475538687844293719286539993743360
                            43100120407759799650887908982784)))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            11298610364653415958880963564018860032
                            872316647418695486453708639648612352)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            10633986225556156197170308812556468224
                            649037107316853453566312041152512)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            11465412901233847296447505758595055616
                            208351686633554403455371421549592576)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          (Code.joinWords 128
                            13293091254233304796575604433234165760
                            689601926524156794414206543724544)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            11465412901233847296447505758595055616
                            208341545467438203847827581514547200)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            10634635265139353129194635674395869184
                            651572408517309912369305447563264)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            664613997892457936451903530140172288
                            664613997892457936451903530140172288)
                          (Code.joinWords 128
                            11465412901233847296447505758595055616
                            207733073179328653735109163975966720))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Code.joinWords 128
                            13292444754903068478151601664397672448
                            43258576732788328326074996883456)))
                      1024))))))
          65536)
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        170141183460469231731687303715884105728
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        170141183460469231731687303715884105728
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      11298437964171784919682360012382928896
                      1024)))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170141183460469231731687303715884105728
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            170143779608898499145501568964048715776
                            128)
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          664613997892457936451903530140172288
                          706152372760736557480147500773933056)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13957056215018445878853365710953906176
                            706152372915479062390820035136323584)
                          256)
                        (Nat.shiftLeft
                          2710541853257309349571011410214780928
                          256))
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128)
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            225968759283435698393647200247658577920))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            225971517691141795020824857073833476096)
                          (Code.joinWords 128
                            42704055654224491656684279033296322560
                            2837763267496214452305220543906316288)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075474015807078423394893019742208
                            128)
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            45196510264393236305907096875706613760))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            213509853112586181324823486279320600576)
                          (Code.joinWords 128
                            213507246822952112085174009057530347520
                            2837763267496214452305220543906316288)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            11299259401760732812334529876060012544
                            706852116056476451577363248703340544)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            10676176172832952128113173888451477504
                            43100120407759799650887908982784)))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            180775007426748558714917760198126862336
                            128)
                          (Code.joinWords 128
                            170141183500083312988819472512656080896
                            180775007466362639972049928994898837504))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            225971517730755876277957025870605582336)
                          (Code.joinWords 128
                            213509843011150203261031115636829323264
                            226854208196861539491247097827004252160)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            180775007466362639972049928994898837504
                            128)
                          (Code.joinWords 128
                            212676479365200620921741298441627107328
                            225968759325525659729350129594228801536))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42537892013546575346736091177135636480
                            45196510264393840768816904190294097920)
                          (Code.joinWords 128
                            168759789261926228673125638687686656
                            179307276091438871381117305196904448)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            3323891427051237574911687514377945088
                            706811551227597741679598320803119104)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            2700806296647556548346229281714601984
                            649037107316853453601496413241344)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            664613997892457936451903530140172288
                            128)
                          (Code.joinWords 128
                            3323891427051237574911687514377945088
                            706852116056476451577398433075429376))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          (Code.joinWords 128
                            2710382129281680592668674625424588800
                            43100120407759799686072281071616)))
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          10633823966279326983230456482242756608
                          256)
                        (Nat.shiftLeft
                          10675362341147605604258700452876517376
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            170143779608898499145501568964048715776)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            11464601604849701229630547868543614976
                            218087243088564700348193567804489728)
                          256)
                        (Nat.shiftLeft
                          10675362341147605604835161205179940864
                          256))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            136
                            128)
                          256)
                        (Nat.shiftLeft
                          2056
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          13292442217125987942401462180813733888
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            2711190890364626203024577722255933440
                            689601926524156794414206543724544)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            830777638570374246400091386300858368
                            218736280195881553801759879845642240)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Nat.shiftLeft
                            651572408517309912369305447563264
                            128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            14123868892803679042255119879155744768
                            218776845063445889927192941336461312)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            43100120407759799650887908982784
                            128)
                          (Code.joinWords 128
                            2711193425665826659629747703551885312
                            43258576732788328326074996883456)))
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679075474015807078423394893019742208
                            128)
                          (Code.joinWords 128
                            170141183460469231740910675752738881536
                            225971355431864965817261298284981387264))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170805797458361689668139207246024278016
                            213509853112586181334046858316175507456)
                          (Code.joinWords 128
                            170805797458361689677362579282879053824
                            226854056088538289911361905630539939840)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10800798903341389359995602228454883328
                            208351686643225810012288454947241984)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            10676173637531751671652119095231381504
                            649037107467969181018140687990784)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            42537892013546575346736091177135636480
                            128)
                          (Code.joinWords 128
                            212676479325586539673832501681709907968
                            2661214399275928373561731699039010816))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            170805797458361689677362579282879053824
                            42704055654224491656684419770784808960)
                          (Code.joinWords 128
                            213507246822952112094433409891404087296
                            2671609820635551638399760183945330688)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10800798903341389359995602228454883328
                            218117666712641584410746522079068160)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            10633823966279326983230456482242756608
                            651572408517309912369305447563264)
                          (Code.joinWords 128
                            10676176172833103243840625717098315776
                            43100120558875527102716555821056)))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2824781891524577269119193554731663360
                            207702649526237550001805109508964352)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            2700157259540239694890411169860288512
                            649037107316853453566312041152512)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2825430928631894122572759866772815872
                            208351686643225810048317801722019840)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          (Code.joinWords 128
                            2711028631087796989805301332321501184
                            689601926675272521866035190562816)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2825430928631894122572759866772815872
                            218726139029765354194216039810596864)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            651572408517309912369305447563264
                            128)
                          (Code.joinWords 128
                            2700806299123474405848852788674560000
                            651572408517309912404489819652096)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            14123047455214731149602950015478661120
                            830767497365572420564879412675215360)
                          (Code.joinWords 128
                            2824609491042946229920590003095732224
                            218117666751327210676733220013211648))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            13292279957849158729038070602803445760
                            43100120407759799650887908982784)
                          (Code.joinWords 128
                            2710382131767421710469545130886955008
                            43258576884494351625645744717824)))
                      1024))))))
          65536)))
    524288)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (2752 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage043
