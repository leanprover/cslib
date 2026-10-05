/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 2689–2752 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage042

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Code.joinWords 262144
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            226802285188507367441389736486508691456
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            170141183460507917358059087037550690304
                            128)
                          (Code.joinWords 128
                            226802133070435340053861556882124046336
                            226854218971892248253560826577209524224)))
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            226635969469526247505956210357097725952)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853152355005086866327610454966272
                            226854218971892248243760844252322463744)
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            226636141830239054783111972577599291392)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            226802295329712169277024921986780889088
                            633825300123914683071091179520)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            14123219855851104693712226101476982784)
                          256)
                        (Nat.shiftLeft
                          14123219855889790320516354987371003904
                          256))
                      1024))))
              16384)
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        32768
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        604462909807314587353088
                        256)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        140737488355328
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        170141183460469231731687303715884105728
                        256)
                      1024)))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            226802295369481597492177597105856053248)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            224143839338142337521417334339573645312
                            673594730700250590828895928320)
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170143779608898499145501568964048715776
                            225971517691141795030624689862991675392)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            224143666937660706492018563577095913472
                            226854218932122817667424936494517714944)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            14123219855851104694432802041856262144)
                          256)
                        (Nat.shiftLeft
                          14123219855696362189378014319418015744
                          256))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            3489233630140205992207705506861547520)
                          256)
                        (Nat.shiftLeft
                          13458595716599102426514438063348776960
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075523533408649838605888984711168
                            830777638763802377538432054253846528)
                          256)
                        (Nat.shiftLeft
                          13292442217319416073539802848766722048
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807089952609939088211968
                            830777638570374247120667326680137728)
                          256)
                        (Nat.shiftLeft
                          13292442217125987943122038121193013248
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075523533408661367820937200664576
                            830777638763802378259007994633125888)
                          256)
                        (Nat.shiftLeft
                          13292442217319416074260378789146001408
                          256))
                      1024))))))
          65536)
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      140737488355328
                      1024)
                    (Nat.shiftLeft
                      144115188075855872
                      1024))
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      2199023255552
                      128)
                    1024)
                  4096))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213343689471908265014875298423159914496
                            226636131689034252957276760603973648384)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            212679724511123123931876961205060894720)
                          (Code.joinWords 128
                            169408826214500577216019416366448640
                            3458784662722723921983754695868416)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10636420114708594397044721730407366656
                            649037107316853453566312041152512)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10844122130254789328021153557201813504
                            652206233817424027070053799165952)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            3489233630140205992207705506861547520
                            207702649371495045091132575146049536)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            144115188075855872
                            2535301200456458802993406410752)
                          (Code.joinWords 128
                            2710382129281680592668674625424588800
                            158456325028528675187087900672)))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            226674911656196434951127347748432510976)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            212676479365200620921885413629703094272)
                          (Code.joinWords 128
                            213509853152355005086866327610454966272
                            226854908573818165585685581746311528448)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            43202506011439033283187994707275808768
                            45902662637308715368297916910842937344)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            659178312118679288778285666795520
                            700376956628605501520953019990016)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            830777638570374246400091386300858368
                            207743214190702348431980469648621568)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458805192429666304
                            128)
                          (Code.joinWords 128
                            10387762843570225832816534230138880
                            43258576732788328326074996883456)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            830818203389581549740939280803430400
                            207702649371495045091132575146049536)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            10425316992601987128835874062598144
                            158456325028528675187087900672)))
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        140737488355328
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          830777638570374246400091386300858368
                          41539008693578735142944718985363456)
                        256)
                      1024))
                  4096)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          8
                          128)
                        256)
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
                            2535301200456458802993406410752
                            2535301200456458802993406410752)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2233382993920
                          128)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          830780173871574702858894379707269120
                          41541544004450598158664745789423616)
                        256)
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            223312899440295134070877223412117274624
                            2661863436383245236238670047934939136)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            224185215453733786938882019521355317248
                            3418219843515430380968649351495680)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2825430928631894122572759866772815872
                            218117666712641584410746522079068160)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            2710382129281680592810538013686759424
                            43258576732788328326074996883456)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10636420114708594397044721730407366656
                            649037107316853453566312041152512)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10677968630781674844487031514028048384
                            651572408517309912378135900323840)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2824612026344146686379392996502142976
                            51926137721520253415725738447863808)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2710379593980480136353986820094033920
                            158456325028528675187087900672)
                          256))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2825258528150263083374156315136884736
                            218766703848972657535063934313693184)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            11036166125586965313545486181859328
                            43100120407759799650887908982784)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166194064292321787453823777037615104
                            218117666751327210638414655669665792)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            10427693837477415056711880567422976
                            2693757525484987478180494311424)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166156034774314940571778875941453824
                            51966860987381178728331786640687104)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10387129018270111862230973954392064
                            40723275532331869523081590472704)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166196599593522243912626770444025856
                            51926296177845281946652725349449728)
                          256)
                        (Nat.shiftLeft
                          10425316992601987128835874062598144
                          256))
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
                      604462909807314587353088
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      38685626227668133590597632
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        604462909807314587353088
                        256)
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          13292442217125987942401462180813733888
                          256)
                        (Nat.shiftLeft
                          41539008693578735142944718985363456
                          256))
                      1024)
                    2048)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            667210146321725350266168778304782336
                            3367366772036664930465418447509520384)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            690235751824270909114954895327232)
                          256))
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
                            223312899440295134061653851375262498816
                            2661863436383245226438837258776739840))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212679724511123123931876961205060894720
                            128)
                          (Code.joinWords 128
                            224143677078865508308053942761563357184
                            3420755144715877039938853599707136)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            38685626227668133590597632
                            128)
                          (Code.joinWords 128
                            13458595716599102426514438063348776960
                            218117666712641584410746522079068160))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Code.joinWords 128
                            2700157259540239694313950417556340736
                            158456325028528675187087900672)))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213343689511522346272007467219931889664
                            226677670103671355340347845905741774848)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            169408865983324339258860747500814336
                            3418259612339182623977191327662080)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            667210146321725350266168778304782336
                            708910780631889337967064166457933824)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            689601926526665551608231042744320)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2825430928631894122572759866772815872
                            218117666741655804081497622272016384)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Code.joinWords 128
                            2710382129281680592668674625424588800
                            43258576732788328326074996883456)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2824650055862153533261437897598304256
                            218077101932119907297566761167093760)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            51964167229855693743105405960060928
                            158456325028528675187087900672)
                          256))
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      590295810358705651712
                      512)
                    1024)
                  2048)
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          8
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          737869762948382064640
                          256)
                        512)
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            40564819207303340847894502572032)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            651572408517309912369305447563264
                            40564819207303340847894502572032)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          13292482781945195245742310075316305920
                          256)
                        (Nat.shiftLeft
                          41579573512786038486044413301620736
                          256))
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212676479325586539664609129644855132160
                            128)
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            225971517691141795030624689862991675392))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212676479325625225300060169815300636672
                            128)
                          (Code.joinWords 128
                            224182609164099717689432709510406864896
                            226854870544145416234469325063156400128)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13292442217125987942401462180813733888
                            10425792371248479269526668910264320)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207893636658253208223744
                            128)
                          (Code.joinWords 128
                            2700159794841440150772753410962751488
                            43258576732788328326074996883456)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            53171715979825902329966547659378393088
                            811296384146066816957890051440640)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            53379417995372097261519440238476263424
                            814465510646637390470462262214656)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            13292444752427188398860265174220144640
                            10387287484266546801456206550401024)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Code.joinWords 128
                            2700157259540239694313950417556340736
                            158456325028528675187087900672)))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2825258528150263083374156315136884736
                            11074195682279438279143332792762368)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2711031166388997446264104325728436224
                            43100120407759799650887908982784)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2658496556389039049148462015063261184
                            10425158584633991382494054149259264)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            51966860987381178728331786640687104
                            2693757525484987478180494311424)
                          256))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2658458526871032202266417113967099904
                            10427693837477415056711880567422976)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Code.joinWords 128
                            2710382129281680592812789813500444672
                            40723275532331869523081590472704)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2658499091690239505607265008469671936
                            10387287484266546801456206550401024)
                          256)
                        (Nat.shiftLeft
                          51964325695852128828697626445611008
                          256))
                      1024))))))
          65536)
        (Nat.shiftLeft
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
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          166163640677916309948187856160686080
                          166164274503216424062888604512288768)
                        256)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          207702649371495045091132575146049536
                          166164274541902050290556738102886400)
                        256)
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            212676479325586539664609129644855132160
                            128)
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            225971355431864965807461465495823187968))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            212679724511123123931876961205060894720)
                          (Code.joinWords 128
                            213509842971381379498988274305694957568
                            226854867969230134511078520483819290624)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            45196510264393236305907096875706613760
                            128)
                          (Code.joinWords 128
                            667210146321725350266168778304782336
                            708910780466833184657804326948831232))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            689601926524156794414206543724544)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10636420114708594397044721730407366656
                            649037107316853453566312041152512)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42704055654224491656684279033296322560
                            651572408517309912369305447563264)
                          (Code.joinWords 128
                            10677968630781674843908177674666770432
                            651572408517309912369305447563264)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2876533093453594620320595714739535872
                            176538727015484253484737623545085952)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            43100120407759799650887908982784
                            128)
                          (Code.joinWords 128
                            2668841219112201515179375861570732032
                            158456325028528675187087900672)))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            45193751856687139678729440049531715584
                            128)
                          (Code.joinWords 128
                            43202506011439033283187994707275808768
                            45902662637308715368297916910842937344))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            649037107316853453566312041152512
                            128)
                          (Code.joinWords 128
                            659178312118679288778285666795520
                            700376956626096744326928520970240)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            45196510264393840768816904190293966848
                            128)
                          (Code.joinWords 128
                            667210146321725350266168778304782336
                            708910780631889337967064166457933824))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            689601926524156794414206543724544
                            128)
                          (Code.joinWords 128
                            649037107316853453566312041152512
                            689601926526665551608231042744320)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            207692508166693219255920601520406528
                            176579291873377183053253651638255616)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            43100120407759799650887908982784
                            128)
                          (Code.joinWords 128
                            10387129018270111715863986064850944
                            43258576732788328326074996883456)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            166153499473114484112975882535043072
                            128)
                          (Code.joinWords 128
                            218117666702970177853829488681418752
                            176538727054169879712405757135683584))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            40723275532331869523081590472704
                            158456325028528675187087900672)))
                      1024)))))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2658618250846660959171005698570977280
                          256)
                        (Nat.shiftLeft
                          2658618884671961073285706446922579968
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          2596148429267413814265248164610048
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          2700157259540239694313950417556340736
                          256)
                        (Nat.shiftLeft
                          2658618884671961073429821634998435840
                          256))
                      1024)))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            689601926524156794414206543724544
                            689601926524156794414206543724544)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            43100120407759799650887908982784
                            2535301200456458802993406410752)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            651572408517309912369305447563264
                            43100120407759799650887908982784)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Code.joinWords 128
                            651572408517309912369305447563264
                            40564819207303340847894502572032)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            51966860987381178728331786640687104
                            2693757525484987478180494311424)
                          256)
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256))
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            53171715979825902329966547659378393088
                            811296384146066816957890051440640)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42701449364590422417034801811506069504
                            649037107316853453566312041152512)
                          (Code.joinWords 128
                            53379417995372097261519440238476263424
                            814465510646637390461631809454080)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2699995000263410480950558839546052608
                            10425158536276958597908887161012224)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            43100120407759799650887908982784
                            128)
                          (Code.joinWords 128
                            2668843754413401971782294043052998656
                            43258576732788328326074996883456)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            10636420114708594397044721730407366656
                            649037107316853453566312041152512)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            42704055654224491656684419770784677888
                            651572408517309912369305447563264)
                          (Code.joinWords 128
                            10677968630781674844487031514028048384
                            651572408517309912378135900323840)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2710382129281680592666422825610903552
                            2693757525484987478180494311424)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            2658455991569831745807614120560689152
                            40564819207303340847894502572032)
                          (Code.joinWords 128
                            2668841219112201515323491049646587904
                            158456325028528675187087900672)))
                      1024)))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            52572639517965243853572023684956160
                            11074195682279438279143332792762368)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            11036166125586965313545486181859328
                            43100120407759799650887908982784)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            51964167229855693740853606146375680
                            10425158574962584825577020751609856)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2535301200456458802993406410752
                            128)
                          (Code.joinWords 128
                            43258576732788328326074996883456
                            2693757526075283288539199963136)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            51926137711848846858808705050214400
                            43258576732788328326074996883456)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            40564819207303340847894502572032
                            128)
                          (Code.joinWords 128
                            10387129018270111859979174140706816
                            40723275532331869525280613728256)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            51966860987381178728331786640687104
                            2693757525484987478180494311424)
                          256)
                        (Nat.shiftLeft
                          40723275532331869523081590472704
                          256))
                      1024))))))
          65536)))
    524288)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (2688 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage042
