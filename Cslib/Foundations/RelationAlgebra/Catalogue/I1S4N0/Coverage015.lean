/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Foundations.RelationAlgebra.Catalogue.I1S4N0.Data
public import Cslib.Foundations.RelationAlgebra.FastCatalogueCoverage

/-!
# Profile coverage for models 961–1024 of the ⟨1, 4, 0⟩ row

The balanced word contains exactly the cycle profiles of this block and its atom renamings.
-/

@[expose] public section

namespace Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage015

/-- The cycle profiles covered by this block of models. -/
def word : ℕ :=
  (Code.joinWords 524288
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            256211292335971801916023076117201027072
                            256212605621993638361899762433789001728)
                          (Code.joinWords 128
                            256212605621993638375572127952532406272
                            256212605621993638375572339883398660096))
                        512)
                      1024)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          256208696187542534502208810869036417024
                          256212605621993638361899762433789001728)
                        (Code.joinWords 128
                          336216433397332841589268848566075392
                          5070602400926806919168489684992))
                      512))
                  4096)
                8192)
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            95704415696513942849074108340184809472
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            127605887595351923798765477786913079296
                            1308215419435532742344597707948032)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            95704415696513942849074108340184809472
                            128)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            95704415696513942849074108340184809472
                            128)
                          256)
                        (Nat.shiftLeft
                          128104348093771267251104405434518208512
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            98362871688083774594881722460745498624
                            128)
                          256)
                        (Nat.shiftLeft
                          1303144817034619824738610895126528
                          256)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          79164837199872
                          128)
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            119630519620642428561342635425231011840
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1308215419435532742344597707948032
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          119630519620642428561342635425231011840
                          128)
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          79164837199872
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          79164837199872
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          119630519620642428561342635425231011840
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          119630519620642428561342635425231011840
                          128)
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            119630519620642428566530782195961823232
                            128)
                          256)
                        (Code.joinWords 256
                          127605887595351923798765477786913079296
                          (Code.joinWords 128
                            128104348093771267251104405434518208512
                            1389978883454846176886227180978176)))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            34559927890407812700687130338019770368
                            128)
                          256)
                        (Code.joinWords 256
                          1298074214633706907132624082305024
                          1303144817034619824738610895126528)))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            34559927890407812700687130338019770368
                            128)
                          256)
                        (Code.joinWords 256
                          128104348093771267251104405434518208512
                          43033756363536651385260753576576155648))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            34559927890407812700687130338019770368
                            128)
                          256)
                        (Code.joinWords 256
                          1303144817034619824738610895126528
                          1303144817034619824738610895126528)))
                    2048))
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
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            34559927890407812701984167030702473216
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            91904668821139269753603098673152
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13292279957849158735523254066216960000
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            83076749755900055170322008062820352)))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749736557242056487941267521536)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            13292279957849158735523254066216960000
                            128)
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            19342813113834066795298816)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          13292279957849158735523254066216960000
                          128)
                        256)))))))
          (Code.joinWords 32768
            (Nat.shiftLeft
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 256
                      (Code.joinWords 128
                        256208696187542534502208810869036417024
                        256212605621993638361899762433789001728)
                      (Code.joinWords 128
                        256212605621993638375572268690020761600
                        256212605621993638375572339883398660096))
                    512)
                  2048)
                4096)
              16384)
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1308215419435532742344597707948032
                            128)
                          256))
                      (Nat.shiftLeft
                        85070591730234615865843651857942052864
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        85070591730234615865843651857942052864
                        256)
                      (Nat.shiftLeft
                        85070591730234615865843651857942052864
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        70368744177664
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          106338239662793269832304564822427566080
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1308849244735646857045346059550720
                            128)
                          256))
                      (Nat.shiftLeft
                        106338239662793269832304564822427566080
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        70368744177664
                        256)
                      (Nat.shiftLeft
                        70368744177664
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        106338239662793269832304564822427566080
                        256)
                      (Nat.shiftLeft
                        106338239662793269832304564822427566080
                        256)))))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          106338239662793269836916250840854953984
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            91904668821139269753603098673152
                            128)
                          256))
                      (Nat.shiftLeft
                        106338239662793269836916250840854953984
                        256))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        106338239662793269836916250840854953984
                        256)
                      (Nat.shiftLeft
                        106338239662793269838069172345461800960
                        256))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            83076749736557242056487941267521536
                            128)
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          106338239662793269838069172345461800960
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            91904668821139269753603098673152
                            128)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          106338239662793269838069172345461800960
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            83076749755900055170322008062820352)))))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749736557242056487941267521536)
                        256)
                      512)
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          106338239662793269838069172345461800960
                          256)
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            19342813113834066795298816
                            19342813113834066795298816)))
                      (Nat.shiftLeft
                        106338239662793269838069172345461800960
                        256))))))))
        131072)
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            127605887595351923798765477786913079296
                            128)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            85735205728127073802295555388082225152
                            1460333491462920270524202092593152)
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256)
                        (Nat.shiftLeft
                          85735205728127073802295555388082225152
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            135581255570061419036188320148595146752
                            128)
                          256)
                        (Nat.shiftLeft
                          85735205728127073802295555388082225152
                          256))
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1379203853048313588828413087449088
                            128)
                          256)
                        (Nat.shiftLeft
                          85901359227600188286408531270617268224
                          256))))
                  4096)
                8192)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            127605887595351923798765477786913079296
                            128)
                          (Nat.shiftLeft
                            135581255570061419036188320148595146752
                            128))
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            107169007180120625386346201167851159552
                            1466037919163947302910102094217216)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          (Nat.shiftLeft
                            1379203853048313588828413087449088
                            128))
                        (Nat.shiftLeft
                          22098415449886009520502549309909106688
                          256)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            135581255570061419036188320148595146752
                            128)
                          (Nat.shiftLeft
                            50510663839826803170344668290653093888
                            128))
                        (Nat.shiftLeft
                          22098415449886009520502549309909106688
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1379203853048313588828413087449088
                            128)
                          (Nat.shiftLeft
                            1379203853048313588828413087449088
                            128))
                        (Nat.shiftLeft
                          22098415449886009520502549309909106688
                          256))))
                  4096)
                8192))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          304592638145092116283392
                          256)
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          304592638145092116283392
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          304592638145092116283392
                          256)
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            107169007160158842252869444235102781440
                            1460333491462920270524202092593152)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          107169007160158842252869444235102781440
                          256)
                        512))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          107169007160158842252869444235102781440
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          107169007160158842252869444235102781440
                          256)
                        512))))
                8192)
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            271165107288552105486190905545354903552
                            128)
                          (Nat.shiftLeft
                            271166648814816925016697519556307976192
                            128))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            271166648751742429304123856995187949568
                            128)
                          (Nat.shiftLeft
                            271166648814817888379460024963931570176
                            128)))
                      1024)
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          271162511140122838072376640297190293504
                          128)
                        (Nat.shiftLeft
                          5321049657833750435936107500239060992
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          271166648751742429304123856995187949568
                          128)
                        (Nat.shiftLeft
                          81192774319972998595216484073472
                          128)))
                    2048))
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
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            22098415454876455303871738543096201216
                            167963704530240395777478011912192)
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
                          (Code.joinWords 128
                            830767522317801337410825578610688000
                            1329227995784915872975864654318272512))))
                    (Code.joinWords 1024
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
                          (Code.joinWords 128
                            830767522317801337410825578610688000
                            72057594037927936)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          830767522317801337410825578610688000
                          256)
                        512)))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      127605887595351923798765477786913079296
                      1298074214633706907132624082305024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            127605887595351923798765477786913079296
                            128)
                          256)
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          135581255570061419036188320148595146752
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1379203853048313588828413087449088
                          128)
                        256)))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504346789367572598259399524352
                            128)
                          256)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            127605887595351923798765477786913079296
                            128)
                          (Nat.shiftLeft
                            50510663839826803170344668290653093888
                            128))
                        (Nat.shiftLeft
                          1303144817034619824808979639304192
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        (Nat.shiftLeft
                          1379203853048313588828413087449088
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            135581255570061419036188320148595146752
                            128)
                          (Nat.shiftLeft
                            45193751856687139678729440049531715584
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625144638033088116424704
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1379203853048313588828413087449088
                            128)
                          (Nat.shiftLeft
                            1379203853048313588828413087449088
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625144638033088116424704
                            128)
                          256))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      304592638145092116283392
                      256)
                    512)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        304592638145092116283392
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1298074214633706907132624082305024
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
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
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          19342813113834066795298816
                          19342813113834066795298816)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
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
                            1349997500136541017613897742434697216
                            128)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625144638033088116424704
                            128)
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 1024
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014718988379809506137066504137474048
                          319014719062656211871330333530332856320)
                        256)
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          319014719062656211871330333530332856320
                          319014719062656211871330333530333773824)
                        256))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          262148
                          128)
                        256)
                      512))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1303144817034619824808979639304192
                        256)
                      512)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625144638033088116424704
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625144638033088116424704
                            128)
                          256)
                        512))))))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      127605887595351923798765477786913079296
                      1298074214633706907132624082305024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            127605887595351923798765477786913079296
                            128)
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1466037919163947302830937257017344
                            128)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          135581255570061419036188320148595146752
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1379203853048313588828413087449088
                          128)
                        256)))
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
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
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            127605887595351923798765477786913079296
                            128)
                          (Nat.shiftLeft
                            50510663839826803170344668290653093888
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            167963704530240395777787249557504
                            128)
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        (Nat.shiftLeft
                          1379203853048313588828413087449088
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            135581255570061419036188320148595146752
                            128)
                          (Nat.shiftLeft
                            45193751856687139678729440049531715584
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            316917485834123911102799544320
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1379203853048313588828413087449088
                            128)
                          (Nat.shiftLeft
                            1379203853048313588828413087449088
                            128))
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4835777066560728623742976
                            128)
                          256))))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            127605887595351923798765477786913079296
                            1389978883150253538741135064694784)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          128104348093771267251104405434518208512
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1303144817034619824738610895126528
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1389978883150253538741135064694784
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1466037919163947302830937257017344
                        128)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          127605887595351923798765477786913079296
                          (Code.joinWords 128
                            43033756363536651385260753576576155648
                            91904668840176309637671355940864))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          1298074214633706907132624082305024
                          1303144817034619824738610895126528)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          128104348093771267251104405434518208512
                          (Code.joinWords 128
                            42701449364590422417034801811506069504
                            316917485834123911102799544320))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          1303144817034619824738610895126528
                          (Code.joinWords 128
                            1303144817034619824738610895126528
                            4835777066560728623742976))
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014718988379809496913694467282698240
                            21267648006835056340877552027535671296)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            21267648006835056340877552027535671296
                            74276402374416639063051075584)
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
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            1412304745521473114960295001547866112)
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            1412304745540815928146186662381355012))))
                    (Code.joinWords 1024
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
                            10775030425569699999476388724736
                            128)))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            83076749755900055170322008062820352))
                        512)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            162893121472140592005867232034816))
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
                            1329227995784915872975864654318272512
                            128))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            72057594037927936
                            128))
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            1412304745521473114960295001547866112)
                          (Code.joinWords 128
                            19342813113834066795298816
                            24178590252452389456969728)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            4835777066560728623742976
                            128)
                          256)
                        512)))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      127605887595351923798765477786913079296
                      1298074214633706907132624082305024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            130264343586921755544573091907473768448
                            128)
                          256)
                        (Nat.shiftLeft
                          1303144817034619824738610895126528
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          128)
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          135581255570061419036188320148595146752
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1379203853048313588828413087449088
                          128)
                        256)))
                  4096))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            127605887595351923798765477786913079296
                            128)
                          (Nat.shiftLeft
                            50510663839826803170344668290653093888
                            128))
                        (Nat.shiftLeft
                          1303144817034619824809254517211136
                          256))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1379203853048313588828413087449088
                          128)
                        (Nat.shiftLeft
                          1379203853048313588828413087449088
                          128)))
                    (Code.joinWords 1024
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          135581255570061419036188320148595146752
                          128)
                        (Nat.shiftLeft
                          45193751856687139678729440049531715584
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1379203853048313588828413087449088
                          128)
                        (Nat.shiftLeft
                          1379203853048313588828413087449088
                          128))))
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1389978883150253538741135064694784
                        128)
                      256)
                    512)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1389978883150253538741135064694784
                          128)
                        256)
                      512)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1303144817034619824738610895126528
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
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
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          1329238770815341442603806536669069312
                          128)))
                    2048)
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
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          128)))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          (Code.joinWords 128
                            83076749755900055170322008062820352
                            83076749755900055170322008062820352))
                        512)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            10775030425569627941882350796800
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
                            83076749755900055170322008062820352))
                        512)))
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749736557242056487941267521536)
                        (Code.joinWords 128
                          1303144836377432938643321312509952
                          19342813113834066795298816))
                      512)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749736557242056487941267521536)
                        (Code.joinWords 128
                          19342813113834066795298816
                          19342813113834066795298816))
                      512)))))))))
    (Code.joinWords 262144
      (Nat.shiftLeft
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      127605887595351923798765477786913079296
                      1298074214633706907132624082305024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      79164837199872
                      128)
                    256)
                  4096))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504346789367571472359492681728
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625070849930876191506432
                            128)
                          256)
                        512))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            83076749736557242056487941267521536
                            83076749736557242056487941267521536)
                          256)
                        512)
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          72057594037927936
                          128)
                        (Nat.shiftLeft
                          72057594037927936
                          128)))
                    (Code.joinWords 1024
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
                            103846254107525199808355096179245056)))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625144638033088116424704
                            128)
                          256)
                        512)))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1298074214633706907132624082305024
                            128)
                          256)
                        (Nat.shiftLeft
                          127605887595351923798765477786913079296
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          128104348093771267251104405434518208512
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1303144817034619824738610895126528
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1298074214633706907132624082305024
                        128)
                      256)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      79164837199872
                      128)
                    256)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1379203853350545043732070381125632
                            128)
                          256)
                        (Code.joinWords 256
                          127605887595351923798765477786913079296
                          43033756363536651385260753576576155648))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          1298074214633706907132624082305024
                          1303144817034619824738610895126528)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          128104348093771267251104405434518208512
                          (Code.joinWords 128
                            42701449364590422417034801811506069504
                            20769504351625144638033088116424704))
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          1303144817034619824738610895126528
                          (Code.joinWords 128
                            1303144817034619824738610895126528
                            20769504351625144638033088116424704))
                        512))
                    2048))
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014719027993890754045863264054673408
                            319014719062656211871330333530332856320)
                          256)
                        (Nat.shiftLeft
                          (Code.joinWords 128
                            319014719062656211871330333530332856320
                            319014719062656211871330333530333773824)
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            262148
                            128)
                          256)
                        512))
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1379203853350545043732070381125632
                        128)
                      256))
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625144638033088116424704
                            128)
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            20769504351625144638033088116424704
                            128)
                          256)
                        512))
                    2048)))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    70368744177664
                    256)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        72057594037927936
                        128)
                      (Nat.shiftLeft
                        72057594037927936
                        128))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749755900055170322008062820352)
                        256)
                      512)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749736557242056487941267521536)
                        (Code.joinWords 128
                          83076749755900055170322008062820352
                          83076749755900055170322008062820352))
                      512))
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1298074214633706907132624082305024
                      128)
                    256)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1298074214633706907132624082305024
                        128)
                      256)
                    2048)
                  (Nat.shiftLeft
                    70368744177664
                    256)))
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1379203853350545043732070381125632
                      128)
                    256)
                  2048)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1379203853369434509663548961980416
                      128)
                    256)
                  2048)))))
        131072)
      (Code.joinWords 131072
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          85070591730234615865843651857942052864
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1460333491462920270524202092593152
                            128)
                          256))
                      (Nat.shiftLeft
                        85070591730234615865843651857942052864
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        85070591730234615865843651857942052864
                        256)
                      (Nat.shiftLeft
                        85070591730234615865843651857942052864
                        256)))
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          271162511140122838072376640297190293504
                          128)
                        (Nat.shiftLeft
                          271166648814817529479607326870895329280
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          271166648751742429304123856995187949568
                          128)
                        (Nat.shiftLeft
                          271166648814817888379460024963931570176
                          128)))
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          106338239682600310460870649220813553664
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            167963704530240395777478011912192
                            128)
                          256))
                      (Nat.shiftLeft
                        106338239682600310460870649220813553664
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        106338239682600310460870649220813553664
                        256)
                      (Nat.shiftLeft
                        106338239687552070618012170320410050560
                        256)))
                  4096)))
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Code.joinWords 4096
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        302231454903657293676544
                        256)
                      1024)
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        302231454903657293676544
                        256)
                      (Nat.shiftLeft
                        302231454903657293676544
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          106338239662793269832304564822427566080
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1460967316763034385224950444195840
                            128)
                          256))
                      (Nat.shiftLeft
                        106338239662793269832304564822427566080
                        256))
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        106338239662793269832304564822427566080
                        256)
                      (Nat.shiftLeft
                        106338239662793269832304564822427566080
                        256))))
                8192)
              (Nat.shiftLeft
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
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)))
                      1024)
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
                        256)))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          106338239687552070618012170320410050560
                          256)
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            167963704530240395777478011912192
                            128)
                          256))
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Code.joinWords 128
                            106338239687552070618012170320410050560
                            1329227995784915872975864654318272512))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128))))
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Code.joinWords 128
                            106338239687552070618012170320410050560
                            72057594037927936))
                        (Code.joinWords 256
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            72057594037927936
                            128)))
                      (Nat.shiftLeft
                        106338239687552070618012170320410050560
                        256))))
                8192)))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1298074214633706907132624082305024
                      256)
                    512)
                  4096)
                8192)
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Code.joinWords 128
                        19342813113834066795298816
                        19342813113834066795298816)
                      512)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1303144817034619824808979639304192
                      256)
                    512)
                  4096)))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    302231454903657293676544
                    256)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      302231454903657293676544
                      256)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1298074214633706907132624082305024
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        256)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          128)
                        256))
                    2048)
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
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          128)))
                    2048))
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1303144817034619824809254517211136
                      256)
                    512)
                  4096)))))
        (Code.joinWords 65536
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      127605887595351923798765477786913079296
                      1298074214633706907132624082305024)
                    2048)
                  4096)
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1466037919163947302830937257017344
                        128)
                      256)
                    512)
                  4096))
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749736557242056487941267521536)
                        (Code.joinWords 128
                          83076749755900055170322008062820352
                          83239642858029382648493808499556352))
                      512)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749736557242056487941267521536)
                        (Code.joinWords 128
                          83076749755900055170322008062820352
                          83076749755900055170322008062820352))
                      512))
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1379203853048313588828413087449088
                            128)
                          256)
                        (Nat.shiftLeft
                          127772041094825038282878453669448122368
                          256))
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1298074214633706907132624082305024
                          256)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          128104348093771267251104405434518208512
                          256)
                        512)
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          1303144817034619824738610895126528
                          256)
                        512))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1379203853048313588828413087449088
                        128)
                      256)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1466037919163947302830937257017344
                        128)
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Code.joinWords 512
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            1379203853369434509663548961980416
                            128)
                          256)
                        (Code.joinWords 256
                          127605887595351923798765477786913079296
                          43033756363536651385260753576576155648))
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          1303144817034619824738610895126528
                          1303144817034619824738610895126528)
                        512))
                    2048)
                  (Nat.shiftLeft
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          128104348093771267251104405434518208512
                          42701449364590422417034801811506069504)
                        512)
                      (Nat.shiftLeft
                        (Code.joinWords 256
                          1303144817034619824738610895126528
                          1303144817034619824738610895126528)
                        512))
                    2048))
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
                          (Nat.shiftLeft
                            1329227995784915872903807060280344576
                            128)
                          (Nat.shiftLeft
                            1329227995784915872975864654318272512
                            128)))
                      1024)
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          1379203853369434581721142999908352
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          72057594037927936
                          128))))
                  (Code.joinWords 2048
                    (Code.joinWords 1024
                      (Nat.shiftLeft
                        (Nat.shiftLeft
                          (Nat.shiftLeft
                            162893102129327478171800436736000
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
                            1329227995784915872975864654318272512
                            128))))
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          72057594037927936
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          72057594037927936
                          128))))))))
          (Code.joinWords 32768
            (Code.joinWords 16384
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1303144817034619824738610895126528
                      256)
                    512)
                  4096)
                8192)
              (Nat.shiftLeft
                (Nat.shiftLeft
                  (Code.joinWords 2048
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749736557242056487941267521536)
                        (Code.joinWords 128
                          84379894572934674995131262580031488
                          83076749755900055170322008062820352))
                      512)
                    (Nat.shiftLeft
                      (Code.joinWords 256
                        (Code.joinWords 128
                          83076749736557242056487941267521536
                          83076749736557242056487941267521536)
                        (Code.joinWords 128
                          83076749755900055170322008062820352
                          83076749755900055170322008062820352))
                      512))
                  4096)
                8192))
            (Code.joinWords 16384
              (Code.joinWords 8192
                (Nat.shiftLeft
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1379203853048313588828413087449088
                      128)
                    256)
                  2048)
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1379203853048313588828413087449088
                        128)
                      256)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1303144817034619824738610895126528
                      256)
                    512)))
              (Code.joinWords 8192
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Code.joinWords 512
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          1330607199638285307485528203280252928
                          128))
                      (Code.joinWords 256
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          128)))
                    2048)
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
                        (Nat.shiftLeft
                          1329227995784915872903807060280344576
                          128)
                        (Nat.shiftLeft
                          1329227995784915872975864654318272512
                          128)))
                    2048))
                (Code.joinWords 4096
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      (Nat.shiftLeft
                        1379203853369434509663548961980416
                        128)
                      256)
                    2048)
                  (Nat.shiftLeft
                    (Nat.shiftLeft
                      1303144817034619824809254517211136
                      256)
                    512)))))))))

/-- The block word is computed from the verified profile data. -/
theorem word_eq :
    Code.profileWord 64 24 (fun i q => Data.profiles (960 + i) q) = word := by
  decide +kernel

end Cslib.RelationAlgebra.Catalogue.I1S4N0.Coverage015
