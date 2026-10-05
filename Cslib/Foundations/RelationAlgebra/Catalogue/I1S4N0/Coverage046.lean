/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 2945–3008 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage046

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Nat.shiftLeft
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Nat.shiftLeft
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213343699662785410917036393927112916992
                            226636141882387923541033528364296568832)
                          256)
                        512)
                      1024)
                    2048)
                  4096)
                8192)
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            223974917289758324584291489657238061056
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
                            224143839338142337521417334339573645312
                            128)
                          256)
                        512)
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213341093323478997601061033174995304448
                            226633373281328156330099103777798750208)
                          256)
                        512)
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            2475880078570760549932466176
                            128)
                          (Code.joinWords 128
                            213341093323478997601061033174995304448
                            223974917289758324584291489657238061056))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213509853112586181324823486279320600576
                            226802295371956873107838550341066948608)
                          256)
                        512)
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212676479365200620921741298441627107328
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223977513438187591998105754905402671104
                            128)
                          (Code.joinWords 128
                            170805797458361689677362579282879053824
                            223977675749612645378507495158929424384)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212679075513630492798465371004379070464
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223977685838669223037304358457038602240
                            128)
                          (Code.joinWords 128
                            170805797458361689677398608079898017792
                            224143839390291206291480744807146455040)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212676479375104141236024340640820101120
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213343689471908265014875298423159914496
                            223977513477801673255237923702174646272)
                          (Code.joinWords 128
                            213343689521580609102766425796574707712
                            226636131741182477124315109279490113536)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212679075523533408649838605888984711168
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213341093323478997601061033174995304448
                            223977523619006475081073135675800289280)
                          (Code.joinWords 128
                            213507246872624456173065136430945140736
                            224143677131013732475092291437079822336)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            212679075523534013112748413203572064256
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213343699613113066840710510396785557504
                            223977685878283304294436527253810577408)
                          (Code.joinWords 128
                            213509853162259132236807803691537006592
                            226802295381861038037288358927707144192)))
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
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            223974917289758324584291489657238061056
                            128)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            226636141830239054783111972577599291392
                            128)
                          256)
                        512)
                      1024))
                  4096)
                8192)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            180775007466362639972049928994898837504
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223977513438187591998105754905402671104
                            128)
                          (Code.joinWords 128
                            212676479325586539673832501681709907968
                            223977523631540617990979315554544779264)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            180775007468838520050620689544697085952
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223977685838669223037304358457038602240
                            128)
                          (Code.joinWords 128
                            212679075474015807087646907667362873344
                            226636141882387923553175383045172101120)))
                      1024))
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            223310303291865866647839586127097888768
                            128)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            36028797027352576
                            128)
                          (Nat.shiftLeft
                            223974917289758324584291489657238061056
                            128)))
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
                            224141070789231439068404465539773104128
                            128)
                          256))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            225971517691141795020824857073833476096
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            226802295329712169277060810046311497728
                            128)
                          256))
                      1024)))
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            223313061699571963287122918751644680192
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            224143839338142337533559189018301693952
                            128)
                          256))
                      1024)
                    2048)
                  4096)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223310303291865866647839586127097888768
                            128)
                          (Nat.shiftLeft
                            225968759335429180055738847591793688576
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223977675697464421220692518520267735040
                            128)
                          (Code.joinWords 128
                            212679075474015807089952609939088211968
                            226636131741182477124315109279490113536)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223312899440295134061653851375262498816
                            128)
                          (Nat.shiftLeft
                            223312899492288615723745498719397609472
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223977513438187592007329126942257446912
                            128)
                          (Code.joinWords 128
                            212676479325586539676138344690923601920
                            224143677131013732475092291437079822336)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223313061699571963275017242953272786944
                            128)
                          (Nat.shiftLeft
                            225971517743135918924758324225446510592
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223977685838669223046527730493893378048
                            128)
                          (Code.joinWords 128
                            212679075474015807089952750676576567296
                            226802295381861038037288358927707144192)))
                      1024))))))
          65536)
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
                            536870912
                            128)
                          (Nat.shiftLeft
                            223977685838669223037304358457575473152
                            128))
                        512)
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213341093323478997601061033174995304448
                            224016455664626603205319733627871821824)
                          256)
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            213343699613113066840710510396785557504
                            226677680888604977594580800826912014336)
                          256)
                        512)
                      1024))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183460469231731687303715884105728
                            180775007468838520050620689544697085952)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223977685838669223037304358457038602240
                            128)
                          (Code.joinWords 128
                            170805797458361689677398608079898017792
                            224019224899511670542510713643596775424)))
                      1024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183500083312988819472512656080896
                            180775007466362639972049928994898837504)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213341093323478997601061033174995304448
                            223977523619006475081073135675800289280)
                          (Code.joinWords 128
                            213341093373151341688952160548410097664
                            224019062006408896612007559525178540032)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            170141183500083312988819472512656080896
                            180775007468838520050620689544697085952)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213343699613113066840710510396785557504
                            223977685878283908757346334568397930496)
                          (Code.joinWords 128
                            213343699662786017752694827806854479872
                            226677680891081502288318327764157464576)))
                      1024))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            223310303291865866647839586127097888768
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            224016455664626603205319733627871821824
                            128)
                          256))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            223313061699571963275017242953272786944
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            224185378346835916268665954856930902016
                            128)
                          256))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            225968759283435698393647200247658577920)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            213341093323478997601061033174995304448
                            128)
                          (Code.joinWords 128
                            213341093323478997601061033174995304448
                            226674911656196434951127347748432510976)))
                      1024)
                    2048)
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            223310303291865866647839586127097888768)
                          256)
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223310303291865866647839586127097888768
                            128)
                          (Code.joinWords 128
                            213507246822952112085174009057530347520
                            224182609164099717689432709510406864896)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          32768
                          (Code.joinWords 128
                            212679075474015807078423394893019742208
                            225971517743135276670810828619596693504))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            53836502378199991305617054741154496512
                            128)
                          (Code.joinWords 128
                            213509853112586181336388730122408034304
                            56702650890470659171363397305125306368)))
                      1024))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223310303291865866647839586127097888768
                            128)
                          (Code.joinWords 128
                            170141183460469231740910675752738881536
                            223310303343859348309931233471232999424))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223977675697464421220692518520267735040
                            128)
                          (Code.joinWords 128
                            170805797458361689677362579282879053824
                            224019214124480923999535739129563185152)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223313061699571963275017242953272786944
                            128)
                          (Code.joinWords 128
                            170141183460469231740910675752738881536
                            223313061751566087178950710102738337792))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223977685838669223046527871231381733376
                            128)
                          (Code.joinWords 128
                            170805797458361689677398608079898017792
                            224185378398984785026623689526131818496)))
                      1024)
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            223310303291865866647839586127097888768
                            128)
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            223310303291865866647839586127097888768))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213341093323478997601061033174995304448
                            223974917289758324584291489657238061056)
                          (Code.joinWords 128
                            213341093323478997601061033174995304448
                            224016455664626603205319733627871821824)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            223310303331479947904971754923869863936)
                          (Code.joinWords 128
                            212676479375104141247553555686888570880
                            225968759335429180055738847591793688576))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213343689471908265014875298423159914496
                            223977675737078502477824687317039710208)
                          (Code.joinWords 128
                            213343689521580609102766425796574707712
                            226677670116050755745343353250123874304)))
                      1024))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212676479325586539664609129644855132160
                            223312899440295134061653851375262498816)
                          (Code.joinWords 128
                            212676479375104141247553555686888570880
                            223312899492288615723745498719397609472))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213341093323478997610284405211850080256
                            223977523619006475090296507712655065088)
                          (Code.joinWords 128
                            213507246872624456173065136430945140736
                            224185215505882011096120535407713583104)))
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Code.joinWords 128
                            212679075474015807078423394893019774976
                            223313061739186648995059219064632115200)
                          (Code.joinWords 128
                            212679075523534013124277768989276372992
                            225971517743135918924758324225446510592))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            213343699613113066849934023171128688640
                            53836502378200595768527002793230204928)
                          (Code.joinWords 128
                            213509853162259132236807803691537006592
                            56702650890471303774388459095034167296)))
                      1024))))))
          65536)))
    524288)

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (2944 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage046
