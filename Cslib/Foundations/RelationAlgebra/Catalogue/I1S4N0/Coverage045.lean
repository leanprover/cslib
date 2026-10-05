/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 2881–2944 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage045

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Code.joinWords 262144
      (Nat.shiftLeft
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
                            223313061699571963275017242953272786944
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            213509853112586181324967601467396456448)
                          (Code.joinWords 128
                            213509853112586181334083028400438509568
                            226843834390564288324258582094726299648)))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            223310303291865866647839586127097888768)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            213509853152200262582099770264168431616)
                          (Code.joinWords 128
                            213509853162297211036636580064356466688
                            226843834390592657793330468896523681792)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            223313061739186044532149411750044762112)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            213509853152200262582099770264168431616)
                          (Code.joinWords 128
                            166153499512406943693234886653509632
                            207692508215050409452721864020328448)))
                      1024))
                  4096))
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            225971517691141795020824857073833476096)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            2868917048647423418076403521881636864)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            225971517691141795020824857073833476096)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            2699995000263410480950558839546052608)
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            225971517691141795020824857073833476096)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            168759789107183723762453104325296128
                            210461057077591672268789401320947712)
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            140737488355328
                            149533581377536)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            2866147865911224850948833973729492992)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            225971517733231756356527786420403699712)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            41539008703250141699861752383012864
                            128)
                          256))
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807089952609939088211968
                            13295038377935298003160991436166397952)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            166325899954745523311579434170974208)
                          (Code.joinWords 128
                            42704055654224491659026150839528980480
                            2876543234668712603455704206086766592)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807089952609939088211968
                            13292442229505426126436918873414434816)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            166153499473114484112975882535043072)
                          (Code.joinWords 128
                            42704055654224491658990263329754185728
                            2710379593990151690484856477527834624)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212676479375104141247553555686888570880
                            225968759332953299977312202230071296000)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213507246822952112085174009057530347520
                            224141070828845520325536634336545079296)
                          (Code.joinWords 128
                            213509853162297211038906252989307027456
                            226843833754291477603056535081134325760)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075523533408661367820935053180928
                            13295038368031777688877949236973404160)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            166163640677916309948187856160686080
                            166325899954745523311579434170974208)
                          (Code.joinWords 128
                            166163640716601936175855989751283712
                            218087243137566483875758219116675072)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075523533408661367820935053180928
                            13292442219601868033222013717059731456)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            168759789107183723762453104325296128
                            166315758749943697476367460545331200)
                          (Code.joinWords 128
                            2606289672754865877286642625019904
                            2710541853295994975945196649391849472)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075523534013124277628251788017664
                            13292442219601905812153876676368924672)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            166153499473114484112975882535043072)
                          (Code.joinWords 128
                            38685626227668133590597632
                            51923602459005570904910490557743104)))
                      1024))))))
          65536)
        131072)
      (Code.joinWords 131072
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            225971517691141795020824857073833476096)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            2868917048647423418076403521881636864)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            225971517691141795020824857073833476096)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            207692508166693219255920601520406528)
                          256))
                      1024))
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            225971517691141795020824857073833476096
                            128)
                          (Nat.shiftLeft
                            225971517733232398598369456692152762368
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            225971517691180480647052525207424073728
                            128)
                          (Code.joinWords 128
                            213343699613113066840710510396785557504
                            226843834380660768012281382904746999808)))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            225971517691141795020824857073833476096
                            128)
                          (Code.joinWords 128
                            212679075523533408649838605888984711168
                            45196510276772636698760899624697856000))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2658628392051462785006217672196620288
                            128)
                          (Code.joinWords 128
                            833373836710671365109921391860252672
                            2876695352769109459914057343851036672)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            225971517691141795020824857073833476096
                            128)
                          (Code.joinWords 128
                            212679075523533408649838605888984711168
                            45196510274297398862031809346648670208))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2658455991569831745807614120560689152
                            128)
                          (Code.joinWords 128
                            830777688281403951295515406207287296
                            218077101932120054873771185016930304)))
                      1024))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            604462909807314587353088
                            2658455991569831745807614120560689152)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            606824093048749409959936
                            2866147865911224850948833973729492992)
                          256))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            2661214399275928372985270946735587328)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            2702763549174308933963427639346593792)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          212679075474015807078423394893019742208
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853112586181334082887113194340352
                            41539008693578735145196518799048704)
                          256))
                      1024)))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            225971517691141795020824857073833476096
                            128)
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            225971517733232398610619247678600511488))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            225971517691180480656275897244278849536
                            128)
                          (Code.joinWords 128
                            213341093323478997601061033174995304448
                            226843834380660768012423096173164756992)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            225971517691141795020824857073833476096
                            128)
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            2658456033660435323496478460537208832))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            225971517691180480656275897244278849536
                            128)
                          (Code.joinWords 128
                            213343699613113066849933882433640333312
                            2699995042518430478866309074521161728)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            225968759283435698393647200247658577920
                            128)
                          (Code.joinWords 128
                            212676479375104141247553555686888570880
                            225971517740659396604489859056246194176))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            226633373281328156339322475814653526016
                            128)
                          (Code.joinWords 128
                            213507246872663141799256775767516774400
                            226843833754291477603056535081134325760)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2661214399275928372985270946735587328
                            128)
                          (Code.joinWords 128
                            212679075523533408661367820935053180928
                            2758407706738869163442285999816704))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2658466132774633571642826094186332160
                            128)
                          (Code.joinWords 128
                            830777688281403948989671847237779456
                            218087243137566483875758219116675072)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2658618250846660959171005698570977280
                            128)
                          (Code.joinWords 128
                            212679075523533408661367820935053180928
                            2658618250846660959315120886646833152))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2658628392051462785006217672196620288
                            128)
                          (Code.joinWords 128
                            833373836710671362804078382646558720
                            2710541853295994975945196649391849472)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2658455991569831745807614120560689152
                            128)
                          (Code.joinWords 128
                            212679075523533408661367961674689019904
                            144115188075855872))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2658455991569831745807614120560689152
                            128)
                          (Code.joinWords 128
                            830777688281403948989672399141076992
                            51923602459005570904910490557743104)))
                      1024))))))
          65536)
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        212679075474015807078423394893019742208
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            2866148499736524965063534722081095680
                            128)
                          256))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            225971517691141795020824857073833476096)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            168759789107183723762453104325296128
                            2827378673779144797048159551247876096)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            225971517740659396592240068069798445056)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            166153499511800110340644016125640704)
                          256))
                      1024))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            225971517691141795020824857073833476096
                            128)
                          (Code.joinWords 128
                            42537892013546575346736091177135636480
                            45196510274297398862031809346648670208))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            2824609491042946229920590003095732224)
                          (Code.joinWords 128
                            42704055654224491658990263329754185728
                            2834994084769687439310772453001658368)))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            225971517691141795020824857073833476096
                            128)
                          (Code.joinWords 128
                            42537892023450095661019133376328630272
                            45196510276772636698760899624697856000))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            168759789107183723762453104325296128
                            2824771750319775443283981581106020352)
                          (Code.joinWords 128
                            168759789145869349990262525160062976
                            2835156977900830838885813373217275904)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            225971517730756480740866833185192804352
                            128)
                          (Code.joinWords 128
                            42537892023450700123928940690915983360
                            45196510274297398862031809346648670208))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            2824609491042946229920590003095732224)
                          (Code.joinWords 128
                            166153499511800110340644016125640704
                            176538093238541319730826466031566848)))
                      1024))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            2661214399275928372985270946735587328)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            2827378673779144797048159551247876096)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            2658455991569831745807614120560689152)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853112586181336352701325389070336
                            2658455991569831745951729308636545024)
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2758407706096627177656826174898176)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            168759789107183723762453104325296128
                            128)
                          (Code.joinWords 128
                            168759789107183723762453104325296128
                            168922682209313051240545430687186944)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2661214399275928372985270946735587328)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2661214399275928372985270946735587328
                            128)
                          (Code.joinWords 128
                            2606289634069239649477221790253056
                            2661225174306030312935183668712833024)))
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2824609491042946229920590003095732224
                            128)
                          (Nat.shiftLeft
                            10384593765426688188013147536228352
                            128))
                        512)
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2661214399275928372985270946735587328
                            128)
                          (Code.joinWords 128
                            42537892013546575349041934186349330432
                            2661214399276570614971056406560505856))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            2824619632247748055755801976721375232)
                          (Code.joinWords 128
                            42704055654224491659026150839528980480
                            2835004859800433982427460235453005824)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2658455991569831745807614120560689152
                            128)
                          (Code.joinWords 128
                            42537892013546575349042074923837685760
                            2658455991569831745951729308636545024))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213509853112586181334046999053663731712
                            2824609491042946229920590003095732224)
                          (Code.joinWords 128
                            42704055654224491658990263329754185728
                            2668840585296572955341911758542471168)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            2658455991569831745807614120560689152)
                          (Code.joinWords 128
                            2596197946868996758691290198048768
                            2661214448793529956650272929148305408))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            2827205679086294910090396084887093248)
                          (Code.joinWords 128
                            168759838818213437845219814311723008
                            2827378089664874397736801453262503936)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2661214399276532835895078261322940416)
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2758407706738869163442285999816704))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            166163640677916309948187856160686080
                            2824619632248352518665609291308728320)
                          (Code.joinWords 128
                            166163640716601936175855989751283712
                            176548868269287862847514248482914304)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2658618250846660959171005698570977280)
                          (Code.joinWords 128
                            2596148429267413814265248164610048
                            2658618250846660959315120886646833152))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            168759789107183723762593841813651456
                            2824771750319775443284122318594375680)
                          (Code.joinWords 128
                            2606289672754865877286642625019904
                            2669003478427716354916952678758088704)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2658455991569831745807614120560689152
                            128)
                          (Nat.shiftLeft
                            144115188075855872
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            166153499473114484112975882535043072
                            2824609491042946229920590003095732224)
                          (Code.joinWords 128
                            38685626227668133590597632
                            10384593765426835761965771572379648)))
                      1024))))))
          65536)))
    524288)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (2880 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage045
